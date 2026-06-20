import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import requests
import threading
import os
import time
import json
import hashlib
import subprocess
import queue
import psutil
import io
import shutil
import concurrent.futures
import ftplib
from urllib.parse import urlparse, unquote, parse_qs
from datetime import datetime
import re
import sys
from http.server import BaseHTTPRequestHandler, HTTPServer


def get_resource_path(relative_path):
    """获取资源的绝对路径（兼容开发环境和PyInstaller打包环境）"""
    try:
        # PyInstaller创建的临时文件夹
        base_path = sys._MEIPASS
    except AttributeError:
        base_path = os.path.abspath(".")
    
    return os.path.join(base_path, relative_path)

class DownloadTask:
    """下载任务类，支持多协议多线程分块下载"""
    DEFAULT_USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/105.0.0.0 Safari/537.36"

    def __init__(self, url, save_path, downloader):
        self.url = url
        self.save_path = save_path
        self.downloader = downloader
        self.download_start_time = None
        self.last_update_time = None
        self.last_downloaded = 0
        self.is_downloading = False
        self.is_paused = False
        self.is_completed = False
        self.downloaded_size = 0
        self.total_size = 0
        self.download_id = None
        self.status = "准备就绪"
        self.progress = 0
        self.task_id = hashlib.md5(f"{url}{save_path}".encode()).hexdigest()
        self.size_info = ""
        self.time_info = ""
        self.tree_item = None
        self.file_hash = None
        self.speed = 0  # 当前下载速度 (字节/秒)
        self.custom_headers = None  # 由外部注入，例如 Cookie 等
        
        # 分块下载相关属性
        self.chunk_size = 1024 * 1024 * 8  # 8MB块大小
        self.chunks = []  # 存储分块下载状态
        self.active_threads = 0
        self.chunk_lock = threading.Lock()
        self.thread_count = self.downloader.thread_var.get()
        self.executor = None
        self.futures = []

        # 读取用户自定义分块大小设置
        self.custom_chunk_size = False
        chunk_size_setting = getattr(downloader, 'chunk_size_setting', None)
        if chunk_size_setting is not None and isinstance(chunk_size_setting, int) and chunk_size_setting > 0:
            self.chunk_size = chunk_size_setting
            self.custom_chunk_size = True
            self.downloader.log_message(f"使用自定义分块大小: {self.downloader.format_size(chunk_size_setting)}")
        else:
            self.chunk_size = 1024 * 1024 * 8  # 8MB 默认值，会被动态覆盖
        
        # 简化的暂停控制
        self.active = True  # 活动状态标志
        # 操作冷却时间控制
        self.last_operation_time = 0  # 上次操作时间戳
        self.operation_cooldown = 3.0  # 需要冷却时间（秒）
        
        # 修改文件名修改状态判断逻辑
        self.original_filename = self.extract_filename(url)
        self.user_filename = os.path.basename(save_path)
        
        # 关键修复：自动生成的文件名不应视为用户修改
        is_auto_generated = re.match(r"download_\d{14}\.bin", self.user_filename)
        self.user_modified = (self.user_filename != self.original_filename) and not is_auto_generated
        self.downloader.log_message(f"文件名状态: 原始={self.original_filename}, 用户={self.user_filename}, 修改={self.user_modified}")
        
        self.verify_chunks = getattr(downloader, 'verify_chunks', True)
        self.chunk_meta_file = None
    
        # 内存缓存配置
        self.use_cache = self.downloader.cache_var.get()
        self.max_cache_size = self.downloader.max_cache_size  # 当前值
        if self.use_cache and self.max_cache_size > 0:
            # 每个分块缓存上限：总缓存除以线程数，至少1MB，最大8MB
            self.chunk_cache_limit = max(1024 * 1024,
                                        min(self.max_cache_size // max(1, self.thread_count),
                                            8 * 1024 * 1024))
        else:
            self.chunk_cache_limit = 0

        

    def extract_filename(self, url):
        """从URL中提取文件名并解码URL编码"""
        try:
            parsed = urlparse(url)
            path = parsed.path
            filename = os.path.basename(path)
            if not filename or '.' not in filename:
                # 生成基于当前时间的文件名
                timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
                return f"download_{timestamp}.bin"
            # 解码URL编码
            return unquote(filename)
        except Exception as e:
            self.downloader.log_message(f"提取文件名错误: {e}")
            return f"download_{int(threading.get_ident())}.bin"
    
    def resolve_redirects(self, session, url):
        """智能选择重定向解析方法"""
        # 对于已知不需要文件名的场景，使用快速解析
        if self.user_modified:
            final_url = self.resolve_redirects_fast(session, url)
            return final_url, None
        else:
            return self.resolve_redirects_comprehensive(session, url)

    def http_download(self):
        """HTTP/HTTPS协议下载处理器"""
        try:
            # 1. 创建会话对象（复用连接）
            session = self.downloader.session
            
            # 2. 处理重定向
            if "github" in self.url or "?" in self.url or "redirect" in self.url or "token" in self.url:
                original_url = self.url
                self.url, real_filename = self.resolve_redirects(session, self.url)
                if real_filename:
                    self.update_filename_from_redirect(real_filename)
                if self.url == original_url:
                    self.downloader.log_message(f"重定向解析未改变原始URL")
                else:
                    self.downloader.log_message(f"解析后的直链: {self.url}")
                
            # 3. 如果是第一次启动，获取文件信息
            if not self.chunks:
                head_resp = session.head(self.url, timeout=10, allow_redirects=True)
                head_resp.raise_for_status()
                self.total_size = int(head_resp.headers.get('content-length', 0))
                supports_range = 'bytes' in head_resp.headers.get('accept-ranges', '')
                if supports_range and self.total_size > 0:
                    self.set_dynamic_chunk_size()
                    self.downloader.pre_connection_manager.pre_connect(self.url, max_connections=5)
                    self._setup_chunks()
                else:
                    self._fallback_single_thread(session)
                    return
                    
            # 6. 启动线程池下载分块
            self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=self.thread_count)
            self.futures = []
            for chunk_id in range(len(self.chunks)):
                if not self.chunks[chunk_id]['completed']:
                    future = self.executor.submit(self._download_chunk, session, chunk_id)
                    self.futures.append(future)
            
            # 等待所有分块完成
            for future in concurrent.futures.as_completed(self.futures):
                if future.exception():
                    raise future.exception()
                    
            # 7. 合并分块文件
            if not self.is_paused:
                self._merge_chunks()
                self._download_complete()
            
        except Exception as e:
            self._handle_error(str(e))
        finally:
            # 关闭线程池，释放资源
            if self.executor:
                try:
                    self.executor.shutdown(wait=False)
                    self.downloader.log_message("HTTP下载线程池已关闭")
                except Exception as e:
                    self.downloader.log_message(f"关闭线程池时发生错误: {e}")

    def resolve_redirects_fast(self, session, url):
        """快速解析重定向链获取最终直链，返回 (final_url, None)"""
        try:
            self.status = "快速解析重定向"
            self.downloader.root.after(0, self.downloader.update_task_row, self)

            # 1. 首先尝试 HEAD 请求（最快）
            try:
                response = session.head(url, allow_redirects=True, timeout=5)
                if response.url != url:
                    self.downloader.log_message(f"HEAD请求重定向: {url} -> {response.url}")
                    return response.url
            except Exception as e:
                self.downloader.log_message(f"HEAD请求失败: {str(e)}")

            # 2. 使用 GET 但只读取头部（中等速度）
            try:
                with session.get(url, stream=True, allow_redirects=True, timeout=5) as response:
                    final_url = response.url
                    if final_url != url:
                        self.downloader.log_message(f"GET头部重定向: {url} -> {final_url}")
                        return final_url
            except Exception as e:
                self.downloader.log_message(f"GET头部请求失败: {str(e)}")

            # 3. 最后尝试完整解析（慢速但兼容性强）
            final_url, _ = self.resolve_redirects_comprehensive(session, url)
            return final_url

        except Exception as e:
            self.downloader.log_message(f"快速解析重定向失败: {str(e)}")
            return url   
        
    def resolve_redirects_comprehensive(self, session, url):
        """全面解析重定向链获取最终直链和真实文件名"""
        try:
            self.status = "全面解析重定向"
            self.downloader.root.after(0, self.downloader.update_task_row, self)
            
            headers = {
                "User-Agent": self.DEFAULT_USER_AGENT,
                "Accept": "*/*",
                "Accept-Language": "en-US,en;q=0.9",
                "Connection": "keep-alive"
            }
            
            # 特别处理 GitHub 资源 URL
            if "github.com" in url or "githubusercontent.com" in url:
                headers.update({
                    "Accept-Encoding": "gzip, deflate, br",
                    "Cache-Control": "no-cache",
                    "Pragma": "no-cache"
                })
            
            with session.get(url, headers=headers, stream=True, allow_redirects=True, timeout=15) as response:
                final_url = response.url
                
                # 记录完整的响应头信息
                self.downloader.log_message(f"响应头信息:\n{json.dumps(dict(response.headers), indent=2)}")
                
                # 获取真实文件名
                real_filename = self.extract_filename_from_headers(response)
                
                # 特别处理 GitHub 资源 URL
                if "github" in url and not real_filename:
                    real_filename = self.extract_github_filename(url, final_url)
                
                # 立即关闭连接避免下载内容
                response.close()
                return final_url, real_filename
        except Exception as e:
            self.downloader.log_message(f"全面解析重定向失败: {str(e)}")
            return url, None

    def extract_filename_from_headers(self, response):
        """从响应头中提取文件名（增强版）"""
        # 1. 尝试从Content-Disposition提取
        content_disposition = response.headers.get('Content-Disposition', '')
        if content_disposition:
            # 增强的Content-Disposition解析
            filename = self.parse_content_disposition(content_disposition)
            if filename:
                self.downloader.log_message(f"从Content-Disposition提取文件名: {filename}")
                return filename
        
        # 2. 尝试从URL路径提取
        parsed = urlparse(response.url)
        path = parsed.path
        filename = os.path.basename(path)
        if filename:
            # 解码URL编码
            filename = unquote(filename)
            # 移除查询参数
            if '?' in filename:
                filename = filename.split('?')[0]
            self.downloader.log_message(f"从URL路径提取文件名: {filename}")
            return filename
        
        # 3. 尝试从原始URL的参数中提取
        original_parsed = urlparse(self.url)
        query_params = parse_qs(original_parsed.query)
        if 'response-content-disposition' in query_params:
            disp = query_params['response-content-disposition'][0]
            filename = self.parse_content_disposition(disp)
            if filename:
                self.downloader.log_message(f"从原始URL参数提取文件名: {filename}")
                return filename
                
        # 4. 生成基于时间戳的默认文件名
        filename = f"download_{datetime.now().strftime('%Y%m%d%H%M%S')}.bin"
        self.downloader.log_message(f"使用默认文件名: {filename}")
        return filename
    
    def parse_content_disposition(self, content_disposition):
        """增强的Content-Disposition解析"""
        # 尝试多种方式提取文件名
        if 'filename*=' in content_disposition:
            # 处理UTF-8编码的文件名: filename*=utf-8''filename.txt
            parts = content_disposition.split("filename*=", 1)
            if len(parts) > 1:
                filename_part = parts[1].split(";")[0].strip()
                if filename_part.lower().startswith("utf-8''"):
                    filename = unquote(filename_part[7:])
                    return filename
                elif filename_part.lower().startswith("iso-8859-1''"):
                    filename = unquote(filename_part[12:])
                    return filename
        
        if 'filename=' in content_disposition:
            # 标准方式: filename="file name.txt"
            parts = content_disposition.split("filename=", 1)
            if len(parts) > 1:
                filename_part = parts[1].split(";")[0].strip()
                
                # 移除引号
                if filename_part.startswith('"') and filename_part.endswith('"'):
                    filename_part = filename_part[1:-1]
                elif filename_part.startswith("'") and filename_part.endswith("'"):
                    filename_part = filename_part[1:-1]
                
                # 处理空格和特殊字符
                filename = unquote(filename_part)
                
                # 处理连续空格
                filename = re.sub(r'\s+', ' ', filename).strip()
                
                return filename
        
        return None
    
    def extract_github_filename(self, original_url, final_url):
        """专门处理GitHub资源URL的文件名提取"""
        # 尝试从原始URL中提取文件名参数
        parsed = urlparse(original_url)
        query = parse_qs(parsed.query)
        
        # 1. 从response-content-disposition参数中提取
        if 'response-content-disposition' in query:
            disp = query['response-content-disposition'][0]
            filename = self.parse_content_disposition(disp)
            if filename:
                self.downloader.log_message(f"从GitHub参数提取文件名: {filename}")
                return filename
        
        # 2. 从filename参数中提取
        if 'filename' in query:
            filename = query['filename'][0]
            self.downloader.log_message(f"从GitHub参数提取文件名: {filename}")
            return filename
        
        # 3. 从final_url中提取
        parsed_final = urlparse(final_url)
        path = parsed_final.path
        filename = os.path.basename(path)
        if filename:
            # 移除查询参数
            if '?' in filename:
                filename = filename.split('?')[0]
            filename = unquote(filename)
            self.downloader.log_message(f"从GitHub最终URL提取文件名: {filename}")
            return filename
        
        # 4. 从原始URL中提取
        path = parsed.path
        filename = os.path.basename(path)
        if filename:
            # 移除查询参数
            if '?' in filename:
                filename = filename.split('?')[0]
            filename = unquote(filename)
            self.downloader.log_message(f"从GitHub原始URL提取文件名: {filename}")
            return filename
        
        return None

    def get_unique_filename(self, filename):
        """获取不冲突的文件名"""
        if not os.path.exists(filename):
            return filename
            
        base, ext = os.path.splitext(filename)
        counter = 1
        new_filename = f"{base}({counter}){ext}"
        
        while os.path.exists(new_filename):
            counter += 1
            new_filename = f"{base}({counter}){ext}"
            
        return new_filename
    
    def update_filename_from_redirect(self, new_filename):
        """根据重定向信息更新文件名（修复逻辑）"""
        if not new_filename:
            self.downloader.log_message("没有获取到新文件名")
            return
        
        # 获取当前保存目录
        save_dir = os.path.dirname(self.save_path)
        
        # 关键修复：无论用户是否修改，都优先使用真实文件名
        if not self.user_modified:
            # 完全使用新文件名
            new_path = os.path.join(save_dir, new_filename)
            # 确保文件名唯一
            unique_path = self.get_unique_filename(new_path)
            self.save_path = unique_path
            self.user_filename = new_filename
            self.downloader.log_message(f"更新完整文件名: {new_filename}")
        else:
            # 用户确实修改了文件名，只更新后缀
            new_basename, new_ext = os.path.splitext(new_filename)
            user_basename, user_ext = os.path.splitext(self.user_filename)
            
            if not user_ext or user_ext.lower() in [".bin", ".download"]:
                # 确保新扩展名有效
                if not new_ext or len(new_ext) < 2 or new_ext[0] != '.':
                    new_ext = os.path.splitext(new_filename)[1] or '.bin'
                
                new_path = os.path.join(save_dir, user_basename + new_ext)
                self.save_path = new_path
                self.downloader.log_message(f"更新后缀: {user_basename}{new_ext}")
            else:
                self.downloader.log_message(f"保留用户自定义文件名: {self.user_filename}")
                
    def get_download_handler(self, url):
        """根据URL协议返回对应的下载处理器"""
        parsed = urlparse(url)
        scheme = parsed.scheme.lower() if parsed.scheme else "http"
        
        if scheme in ('http', 'https'):
            return self.http_download
        elif scheme == 'ftp':
            return self.ftp_download
        elif scheme == 'file':
            return self.file_download
        elif scheme == 'blob':
            return self.blob_download
        else:
            self._handle_error(f"不支持的URL协议: {scheme}")
            return None
    
    def start_multithread_download(self):
        """启动多线程分块下载"""
        self.is_downloading = True
        self.is_paused = False
        self.status = "下载中"
        
        if self.download_start_time is None:
            self.download_start_time = time.time()
        self.last_update_time = time.time()
        self.last_downloaded = self.downloaded_size
        
        try:
            session = self.downloader.session
            self.downloader.log_message(f"开始处理重定向: {self.url}")
            original_url = self.url
            self.url, real_filename = self.resolve_redirects(session, self.url)
            if real_filename:
                self.downloader.log_message(f"获取到真实文件名: {real_filename}")
                self.update_filename_from_redirect(real_filename)
                self.downloader.log_message(f"更新后保存路径: {self.save_path}")
            if self.url == original_url:
                self.downloader.log_message(f"重定向解析未改变原始URL")
            else:
                self.downloader.log_message(f"解析后的直链: {self.url}")
            
            if not self.chunks:
                try:
                    head_resp = session.head(self.url, timeout=5, allow_redirects=True)
                    head_resp.raise_for_status()
                except requests.RequestException:
                    try:
                        with session.get(self.url, stream=True, timeout=5) as r:
                            self.total_size = int(r.headers.get('content-length', 0))
                            supports_range = 'bytes' in r.headers.get('accept-ranges', '')
                    except:
                        with session.get(self.url, stream=True, timeout=10) as r:
                            self.total_size = int(r.headers.get('content-length', 0))
                            supports_range = 'bytes' in r.headers.get('accept-ranges', '')
                else:
                    self.total_size = int(head_resp.headers.get('content-length', 0))
                    supports_range = 'bytes' in head_resp.headers.get('accept-ranges', '')
                
                if supports_range and self.total_size > 0:
                    self.set_dynamic_chunk_size()
                    self.downloader.pre_connection_manager.pre_connect(self.url, max_connections=10)
                    self._setup_chunks()
                else:
                    self._fallback_single_thread(session)
                    return
                    
            self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=self.thread_count)
            self.futures = []
            for chunk_id in range(len(self.chunks)):
                if not self.chunks[chunk_id]['completed']:
                    future = self.executor.submit(self._download_chunk, session, chunk_id)
                    self.futures.append(future)
            
            for future in concurrent.futures.as_completed(self.futures):
                if future.exception():
                    raise future.exception()
                    
            if not self.is_paused:
                self._merge_chunks()
                self._download_complete()
            
        except Exception as e:
            self._handle_error(str(e))
        finally:
            self.is_downloading = False
            self.downloader.save_resume_info()

    def set_dynamic_chunk_size(self):
        """根据文件大小动态设置分块大小（若用户已自定义则跳过）"""
        if getattr(self, 'custom_chunk_size', False):
            self.downloader.log_message(f"保留用户自定义分块大小: {self.downloader.format_size(self.chunk_size)}")
            return
            
        if self.total_size < 100 * 1024 * 1024:  # < 100MB
            self.chunk_size = 1024 * 1024  # 1MB
        elif self.total_size < 1024 * 1024 * 1024:  # < 1GB
            self.chunk_size = 1024 * 1024 * 8  # 8MB
        else:
            self.chunk_size = 1024 * 1024 * 16  # 16MB
     
    def ftp_download(self):
        """FTP协议下载处理器"""
        self.status = "FTP下载中"
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        
        try:
            parsed = urlparse(self.url)
            hostname = parsed.hostname
            port = parsed.port or 21
            path = parsed.path
            
            # 连接到FTP服务器
            ftp = ftplib.FTP()
            ftp.connect(hostname, port)
            ftp.login()  # 匿名登录
            
            # 获取文件大小
            self.total_size = ftp.size(path)
            if not self.total_size or self.total_size <= 0:
                self._handle_error("无法获取FTP文件大小")
                return
                
            # 创建文件
            with open(self.save_path, 'wb') as f:
                def callback(data):
                    if not self.active or self.is_paused:
                        raise Exception("下载已暂停")
                    f.write(data)
                    self.downloaded_size += len(data)
                    # 定期更新UI
                    if time.time() - self.last_update_time > 0.1:
                        self._update_progress()
                
                # 下载文件
                ftp.retrbinary(f"RETR {path}", callback, blocksize=1024 * 1024)
            
            # 检查下载是否完成
            if os.path.getsize(self.save_path) == self.total_size:
                self._download_complete()
            else:
                self._handle_error("FTP下载不完整")
                
        except Exception as e:
            self._handle_error(f"FTP错误: {str(e)}")
    
    def file_download(self):
        """file://协议下载处理器（本地文件复制）"""
        self.status = "复制本地文件"
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        
        try:
            parsed = urlparse(self.url)
            # 处理Windows路径 (file:///C:/path/to/file)
            if parsed.path.startswith('/'):
                source_path = parsed.path[1:]
            else:
                source_path = parsed.path
                
            # 获取绝对路径
            source_path = os.path.abspath(source_path)
            
            # 获取文件大小
            self.total_size = os.path.getsize(source_path)
            
            # 显示进度
            self.downloaded_size = 0
            self._update_progress()
            
            # 复制文件（模拟下载）
            with open(source_path, 'rb') as src, open(self.save_path, 'wb') as dst:
                while True:
                    if not self.active or self.is_paused:
                        self._handle_error("复制已暂停")
                        return
                        
                    data = src.read(1024 * 1024 * 10)  # 10MB chunks
                    if not data:
                        break
                    dst.write(data)
                    self.downloaded_size += len(data)
                    self._update_progress()
            
            # 检查复制是否成功
            if os.path.getsize(self.save_path) == self.total_size:
                self._download_complete()
            else:
                self._handle_error("文件复制失败")
                
        except Exception as e:
            self._handle_error(f"文件复制错误: {str(e)}")
    
    def blob_download(self):
        """blob:协议下载处理器（需要特殊处理）"""
        self.status = "处理Blob资源"
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        
        try:
            # 尝试从blob URL中提取资源ID
            if 'blob:' in self.url:
                blob_id = self.url.split('blob:')[-1]
                self.downloader.log_message(f"解析Blob资源ID: {blob_id}")
                
                # 在实际应用中，这里可以调用浏览器扩展或本地服务
                # 但这里我们简单地将blob转换为data URL（示例）
                self.url = f"data:application/octet-stream;base64,{blob_id}"
                self.data_uri_download()
            else:
                self._handle_error("无效的Blob URL格式")
            
        except Exception as e:
            self._handle_error(f"Blob资源处理失败: {str(e)}")
    
    def data_uri_download(self):
        """data: URI协议下载处理器"""
        self.status = "下载Data URI资源"
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        
        try:
            if not self.url.startswith("data:"):
                self._handle_error("无效的Data URI")
                return
                
            # 解析Data URI
            header, data = self.url.split(",", 1)
            parts = header.split(";")
            
            # 解码Base64数据
            if "base64" in parts:
                import base64
                file_data = base64.b64decode(data)
            else:
                import urllib.parse
                file_data = urllib.parse.unquote(data).encode()
            
            # 获取文件大小
            self.total_size = len(file_data)
            
            # 写入文件
            with open(self.save_path, "wb") as f:
                f.write(file_data)
            
            self.downloaded_size = self.total_size
            self._download_complete()
                
        except Exception as e:
            self._handle_error(f"Data URI下载错误: {str(e)}")
    
    def pause_download(self):
        """暂停下载任务 - 添加操作冷却时间检查"""
        current_time = time.time()
        if current_time - self.last_operation_time < self.operation_cooldown:
            # 显示冷却中提示
            self.status = f"操作冷却中: {(self.operation_cooldown - (current_time - self.last_operation_time)):.1f}秒"
            self.downloader.root.after(0, self.downloader.update_task_row, self)
            self.downloader.log_message(f"操作过快: 暂停请求被忽略")
            return
            
        self.last_operation_time = current_time
        
        self.active = False
        self.is_paused = True
        self.status = "已暂停"
        
        # 更新UI
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        self.downloader.log_message(f"任务已暂停: {os.path.basename(self.save_path)}")
    
    def resume_download(self):
        """继续下载任务 - 添加操作冷却时间和网络检查（保留原有功能）"""
        if self.is_completed:
            return
        # 防止重复启动
        if self.is_downloading and not self.is_paused:
            return
            
        current_time = time.time()
        if current_time - self.last_operation_time < self.operation_cooldown:
            # 显示冷却中提示（原有逻辑）
            self.status = f"操作冷却中: {(self.operation_cooldown - (current_time - self.last_operation_time)):.1f}秒"
            self.downloader.root.after(0, self.downloader.update_task_row, self)
            self.downloader.log_message(f"操作过快: 继续请求被忽略")
            return
            
        self.last_operation_time = current_time
        
        # 原有继续下载逻辑
        self.active = True
        self.is_paused = False
        self.status = "下载中"
        
        # 更新UI
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        
        # 启动下载线程
        threading.Thread(target=self.start_multithread_download, daemon=True).start()
        self.downloader.log_message(f"任务已继续: {os.path.basename(self.save_path)}")
        
    def _setup_chunks(self):
        """
        初始化分块下载信息，支持断点续传和完整性校验。
        1. 创建临时目录和元数据文件 (meta.json)
        2. 加载已有的分块状态
        3. 校验每个分块的大小和哈希（如启用）
        4. 更新全局已下载大小
        """
        # 确保临时目录存在
        temp_dir = os.path.join(os.path.dirname(self.save_path), f".{self.task_id}")
        os.makedirs(temp_dir, exist_ok=True)
        self.chunk_meta_file = os.path.join(temp_dir, "meta.json")
        
        # 加载已有元数据（存储每个分块的哈希和大小）
        meta = {}
        if os.path.exists(self.chunk_meta_file):
            try:
                with open(self.chunk_meta_file, 'r') as f:
                    meta = json.load(f)
            except Exception as e:
                self.downloader.log_message(f"加载分块元数据失败: {e}，将重新初始化")
        
        # 计算分块数量
        chunk_count = max(1, (self.total_size + self.chunk_size - 1) // self.chunk_size)
        self.chunks = []
        self.downloaded_size = 0
        
        for i in range(chunk_count):
            start = i * self.chunk_size
            end = min((i + 1) * self.chunk_size - 1, self.total_size - 1)
            expected_size = end - start + 1
            chunk_file = os.path.join(temp_dir, f"part{i}")
            
            # 从元数据中获取该分块的信息
            stored_meta = meta.get(str(i), {})
            stored_hash = stored_meta.get('hash', '')
            stored_size = stored_meta.get('size', 0)
            
            # 检查本地文件是否存在
            if os.path.exists(chunk_file):
                actual_size = os.path.getsize(chunk_file)
                # 启用校验且元数据中有哈希时，进行完整性验证
                if self.verify_chunks and stored_hash:
                    actual_hash = self._compute_file_hash(chunk_file)
                    if actual_size == expected_size and actual_hash == stored_hash:
                        # 完全匹配，视为已完成
                        completed = True
                        downloaded = actual_size
                    else:
                        # 不匹配：删除损坏的分块，重置状态
                        self.downloader.log_message(
                            f"分块 {i} 校验失败 (大小:{actual_size}/{expected_size}, 哈希不匹配)，将重新下载"
                        )
                        try:
                            os.remove(chunk_file)
                        except:
                            pass
                        completed = False
                        downloaded = 0
                else:
                    # 未启用校验或没有哈希，仅按大小判断（兼容旧版）
                    if actual_size == expected_size:
                        completed = True
                        downloaded = actual_size
                    else:
                        # 大小不符，重置
                        self.downloader.log_message(f"分块 {i} 大小不符 ({actual_size}/{expected_size})，将重新下载")
                        try:
                            os.remove(chunk_file)
                        except:
                            pass
                        completed = False
                        downloaded = 0
            else:
                # 文件不存在，初始状态
                completed = False
                downloaded = 0
            
            chunk_data = {
                'id': i,
                'start': start,
                'end': end,
                'downloaded': downloaded,
                'completed': completed,
                'file': chunk_file,
                'hash': stored_hash if completed else None   # 如果已完成，保留哈希
            }
            self.chunks.append(chunk_data)
            self.downloaded_size += downloaded
        
        # 如果所有分块都已下载完毕，但总大小与预期不符（极少情况），以实际大小为准
        if self.downloaded_size > self.total_size:
            self.downloaded_size = self.total_size
            
    def _compute_file_hash(self, file_path, algorithm='sha256'):
        """计算文件的哈希值，使用分块读取避免内存溢出"""
        import hashlib
        hash_func = hashlib.sha256()
        with open(file_path, 'rb') as f:
            for chunk in iter(lambda: f.read(1024 * 1024), b''):  # 1MB块
                hash_func.update(chunk)
        return hash_func.hexdigest()

    def _save_chunk_meta(self, chunk_id, hash_value):
        """将分块的哈希和大小保存到 meta.json"""
        if not self.chunk_meta_file:
            return
        try:
            with open(self.chunk_meta_file, 'r') as f:
                meta = json.load(f)
        except:
            meta = {}
        chunk = self.chunks[chunk_id]
        meta[str(chunk_id)] = {
            'size': chunk['end'] - chunk['start'] + 1,
            'hash': hash_value
        }
        with open(self.chunk_meta_file, 'w') as f:
            json.dump(meta, f, indent=2)

    def _download_chunk(self, session, chunk_id):
        """
        下载单个分块（支持断点续传、重试、完整性校验）
        支持内存缓存：数据先写入内存缓冲区，达到阈值后刷入磁盘
        """
        chunk = self.chunks[chunk_id]
        if chunk['completed']:
            return

        with self.chunk_lock:
            self.active_threads += 1

        try:
            max_retries = 5
            retry_count = 0
            wait_time = 1

            while retry_count < max_retries and self.active:
                try:
                    chunk_dir = os.path.dirname(chunk['file'])
                    os.makedirs(chunk_dir, exist_ok=True)

                    # 检查已有文件大小（断点续传）
                    if os.path.exists(chunk['file']):
                        current_size = os.path.getsize(chunk['file'])
                        if current_size > (chunk['end'] - chunk['start'] + 1):
                            os.remove(chunk['file'])
                            current_size = 0
                        chunk['downloaded'] = current_size
                    else:
                        chunk['downloaded'] = 0

                    expected_size = chunk['end'] - chunk['start'] + 1
                    if chunk['downloaded'] == expected_size:
                        chunk['completed'] = True
                        if self.verify_chunks:
                            chunk_hash = self._compute_file_hash(chunk['file'])
                            chunk['hash'] = chunk_hash
                            self._save_chunk_meta(chunk_id, chunk_hash)
                        return

                    headers = {
                        'Range': f'bytes={chunk["start"] + chunk["downloaded"]}-{chunk["end"]}',
                        'Connection': 'keep-alive'
                    }
                    # 对大文件禁用压缩，避免 CPU 开销
                    if self.total_size > 100 * 1024 * 1024:  # 大于 100MB 禁用
                        headers['Accept-Encoding'] = 'identity'  # 明确要求不压缩
                    else:
                        headers['Accept-Encoding'] = 'gzip, deflate, br'
                        
                    if self.custom_headers:
                        headers.update(self.custom_headers)

                    with session.get(self.url, headers=headers, stream=True, timeout=30) as r:
                        r.raise_for_status()

                        # 打开文件（追加模式）用于刷入缓存数据
                        # 使用 'ab' 模式，文件指针在末尾
                        f = open(chunk['file'], 'ab')

                        # 创建内存缓冲区
                        buffer = io.BytesIO()
                        buffer_limit = self.chunk_cache_limit  # 如果为0则不启用缓存

                        try:
                            for data in r.iter_content(chunk_size=1024 * 512):  # 512KB 块
                                if not self.active:
                                    return

                                # 写入缓冲区
                                buffer.write(data)
                                chunk['downloaded'] += len(data)
                                with self.chunk_lock:
                                    self.downloaded_size += len(data)

                                # 如果缓冲区达到限制，刷入磁盘
                                if buffer_limit > 0 and buffer.tell() >= buffer_limit:
                                    f.write(buffer.getvalue())
                                    f.flush()
                                    buffer.seek(0)
                                    buffer.truncate()

                                if time.time() - self.last_update_time > 0.1:
                                    self._update_progress()

                            # 写入剩余缓存数据
                            if buffer.tell() > 0:
                                f.write(buffer.getvalue())
                                f.flush()
                        finally:
                            f.close()
                            buffer.close()

                        # 检查下载完整性
                        actual_size = os.path.getsize(chunk['file'])
                        if actual_size == expected_size:
                            if self.verify_chunks:
                                chunk_hash = self._compute_file_hash(chunk['file'])
                                chunk['hash'] = chunk_hash
                                self._save_chunk_meta(chunk_id, chunk_hash)
                            chunk['completed'] = True
                            self.downloader.log_message(f"分块 {chunk_id} 下载完成")
                            break
                        else:
                            raise Exception(f"分块 {chunk_id} 大小不符: {actual_size} vs {expected_size}")

                except (requests.ConnectionError, requests.Timeout, requests.exceptions.ChunkedEncodingError) as e:
                    retry_count += 1
                    if retry_count < max_retries:
                        wait_time = 2 ** retry_count
                        self.downloader.log_message(f"分块 {chunk_id} 网络错误，{wait_time}s 后重试 (尝试 {retry_count}/{max_retries}): {str(e)}")
                        time.sleep(wait_time)
                    else:
                        self.downloader.log_message(f"分块 {chunk_id} 网络错误，超过最大重试次数: {str(e)}")
                        self.status = "网络错误"
                        self.downloader.root.after(0, self.downloader.update_task_row, self)
                        return

                except Exception as e:
                    retry_count += 1
                    if retry_count < max_retries:
                        wait_time = 2 ** retry_count
                        self.downloader.log_message(f"分块 {chunk_id} 错误，{wait_time}s 后重试 (尝试 {retry_count}/{max_retries}): {str(e)}")
                        time.sleep(wait_time)
                    else:
                        self.downloader.log_message(f"分块 {chunk_id} 下载失败，超过最大重试次数: {str(e)}")
                        self.status = f"分块错误: {str(e)[:50]}"
                        self.downloader.root.after(0, self.downloader.update_task_row, self)
                        return

            if not self.active:
                self.downloader.log_message(f"分块 {chunk_id} 因暂停/取消而中断")
                return

            if chunk['completed'] and self.verify_chunks and chunk.get('hash') is None:
                try:
                    chunk_hash = self._compute_file_hash(chunk['file'])
                    chunk['hash'] = chunk_hash
                    self._save_chunk_meta(chunk_id, chunk_hash)
                except Exception as e:
                    self.downloader.log_message(f"保存分块 {chunk_id} 哈希失败: {e}")

        finally:
            with self.chunk_lock:
                self.active_threads -= 1

    def _fallback_single_thread(self, session):
        """服务器不支持分块时使用单线程下载"""
        # 处理重定向
        if "github" in self.url or "?" in self.url or "redirect" in self.url or "token" in self.url:
            final_url, real_filename = self.resolve_redirects(session, self.url)
            if real_filename:
                self.update_filename_from_redirect(real_filename)
            
            self.downloader.log_message(f"单线程使用直链: {final_url}")
            self.url = final_url
        else:
            final_url = self.url
        
        try:
            # 特殊处理crsky.com
            headers = {
                "User-Agent": self.DEFAULT_USER_AGENT,
                "Accept": "*/*",
                "Connection": "keep-alive"
            }
            
            if "crsky.com" in self.url:
                headers.update({
                    "Accept-Encoding": "gzip, deflate, br",
                    "Accept-Language": "zh-CN,zh;q=0.9",
                    "Cache-Control": "no-cache",
                    "Pragma": "no-cache"
                })
            
            with session.get(final_url, headers=headers, stream=True, timeout=45) as r:
                # 处理HTTP 501错误
                if r.status_code == 501:
                    self._handle_error("服务器不支持此操作(501 Not Implemented)")
                    return
                
                r.raise_for_status()
                
                # 获取总大小
                self.total_size = int(r.headers.get('content-length', 0))
                
                # 创建文件
                with open(self.save_path, 'wb') as f:
                    for data in r.iter_content(chunk_size=1024 * 1024):  # 1MB chunks
                        if self.is_paused:
                            return
                            
                        f.write(data)
                        self.downloaded_size += len(data)
                        self._update_progress()
                        
                if not self.is_paused:
                    self._download_complete()
        except Exception as e:
            self._handle_error(str(e))
    
    def _merge_chunks(self):
        """
        合并所有分块文件到目标文件，支持完整性校验和自动修复。
        优化：记录每个分块的重试次数，避免重复修复同一分块。
        """
        temp_dir = os.path.join(os.path.dirname(self.save_path), f".{self.task_id}")
        max_repair_attempts = 3          # 每个分块最多尝试修复次数
        repair_attempts = {}             # {chunk_id: 尝试次数}

        # 循环直到所有分块都完整
        while True:
            # 1. 检查所有分块的完整性和存在性
            missing_chunks = []
            corrupted_chunks = []

            for chunk in self.chunks:
                chunk_file = chunk['file']
                expected_size = chunk['end'] - chunk['start'] + 1

                if not os.path.exists(chunk_file):
                    self.downloader.log_message(f"分块 {chunk['id']} 文件缺失: {chunk_file}")
                    missing_chunks.append(chunk)
                    continue

                actual_size = os.path.getsize(chunk_file)
                if actual_size != expected_size:
                    self.downloader.log_message(f"分块 {chunk['id']} 大小不符: {actual_size} vs {expected_size}")
                    corrupted_chunks.append(chunk)
                    continue

                if self.verify_chunks and chunk.get('hash'):
                    actual_hash = self._compute_file_hash(chunk_file)
                    if actual_hash != chunk['hash']:
                        self.downloader.log_message(f"分块 {chunk['id']} 哈希不匹配")
                        corrupted_chunks.append(chunk)
                        continue

            # 2. 如果没有缺失或损坏，跳出循环，开始合并
            if not missing_chunks and not corrupted_chunks:
                break

            # 3. 构建需要修复的分块列表，并检查重试次数
            need_repair = missing_chunks + corrupted_chunks
            to_repair = []
            for chunk in need_repair:
                cid = chunk['id']
                attempts = repair_attempts.get(cid, 0)
                if attempts >= max_repair_attempts:
                    raise Exception(f"分块 {cid} 修复失败次数过多 ({max_repair_attempts} 次)")
                to_repair.append(chunk)

            if not to_repair:
                raise Exception("需要修复的分块均已达到最大重试次数，无法继续")

            # 4. 执行修复
            self.downloader.log_message(f"需要修复 {len(to_repair)} 个分块")
            repair_success, failed_chunks = self._repair_chunks_with_failed(to_repair)

            if not repair_success:
                # 增加失败分块的重试计数
                for chunk in failed_chunks:
                    cid = chunk['id']
                    repair_attempts[cid] = repair_attempts.get(cid, 0) + 1
                    self.downloader.log_message(f"分块 {cid} 修复失败，尝试次数 {repair_attempts[cid]}")
                # 继续循环，重新检查所有分块
                continue
            else:
                self.downloader.log_message("所有需要修复的分块已成功下载")
                # 更新全局下载进度（保险）
                total_downloaded = sum(c['downloaded'] for c in self.chunks if c['completed'])
                self.downloaded_size = total_downloaded
                # 继续循环，以确保所有分块确实完整
                continue

        # ========== 所有分块完整，开始合并 ==========
        try:
            # 确保输出目录存在
            os.makedirs(os.path.dirname(self.save_path), exist_ok=True)
            # 如果目标文件已存在（可能是不完整的），先删除
            if os.path.exists(self.save_path):
                try:
                    os.remove(self.save_path)
                except Exception as e:
                    self.downloader.log_message(f"删除旧目标文件失败: {e}")

            self.downloader.log_message(f"开始合并 {len(self.chunks)} 个分块到 {self.save_path}")
            with open(self.save_path, 'wb') as outfile:
                for chunk in self.chunks:
                    chunk_file = chunk['file']
                    if not os.path.exists(chunk_file):
                        raise Exception(f"合并过程中发现分块 {chunk['id']} 丢失")
                    with open(chunk_file, 'rb') as infile:
                        shutil.copyfileobj(infile, outfile, 1024 * 1024 * 16)  # 16MB缓冲区

            # 验证最终文件大小
            final_size = os.path.getsize(self.save_path)
            if final_size != self.total_size:
                raise Exception(f"合并后文件大小 {final_size} 与预期 {self.total_size} 不符")

            # 可选：计算最终文件的哈希
            # if self.verify_chunks:
            #     final_hash = self._compute_file_hash(self.save_path)
            #     self.downloader.log_message(f"最终文件哈希: {final_hash}")

            # 清理临时文件
            self._cleanup_temp_files(temp_dir)
            self.downloader.log_message("合并成功，临时文件已清理")
            return

        except Exception as e:
            # 合并失败，清理部分合并文件并重新抛出
            if os.path.exists(self.save_path):
                try:
                    os.remove(self.save_path)
                except:
                    pass
            raise Exception(f"合并失败: {e}")

    def _repair_chunks_with_failed(self, chunks_to_repair):
        """
        修复指定的分块列表，返回 (是否全部成功, 失败的分块列表)
        """
        if not chunks_to_repair:
            return True, []

        self.downloader.log_message(f"开始修复 {len(chunks_to_repair)} 个分块")
        failed = []

        for chunk in chunks_to_repair:
            chunk_id = chunk['id']
            # 重置分块状态
            chunk['completed'] = False
            chunk['downloaded'] = 0
            chunk['hash'] = None
            if os.path.exists(chunk['file']):
                try:
                    os.remove(chunk['file'])
                except:
                    pass

            try:
                self._download_chunk(self.downloader.session, chunk_id)
                if not chunk['completed']:
                    self.downloader.log_message(f"分块 {chunk_id} 修复后仍未完成")
                    failed.append(chunk)
                else:
                    self.downloader.log_message(f"分块 {chunk_id} 修复成功")
            except Exception as e:
                self.downloader.log_message(f"修复分块 {chunk_id} 时发生异常: {e}")
                failed.append(chunk)

        if failed:
            self.downloader.log_message(f"{len(failed)} 个分块修复失败")
            return False, failed
        else:
            return True, []

    def _repair_chunks(self, chunks_to_repair):
        """
        修复指定的分块列表（缺失或损坏），使用 _download_chunk 重新下载。
        参数:
            chunks_to_repair: 需要修复的分块列表
        返回:
            bool: 是否全部成功修复
        """
        if not chunks_to_repair:
            return True

        self.downloader.log_message(f"开始修复 {len(chunks_to_repair)} 个分块")
        repair_success = True

        # 按分块ID排序，便于追踪
        chunks_to_repair.sort(key=lambda c: c['id'])

        for chunk in chunks_to_repair:
            # 重置分块状态，删除旧文件
            chunk['completed'] = False
            chunk['downloaded'] = 0
            chunk['hash'] = None
            if os.path.exists(chunk['file']):
                try:
                    os.remove(chunk['file'])
                except:
                    pass

            # 调用 _download_chunk 重新下载（会更新self.chunks和元数据）
            # 注意：_download_chunk 需要 session 和 chunk_id
            try:
                self._download_chunk(self.downloader.session, chunk['id'])
                # 检查下载后是否标记为完成
                if not chunk['completed']:
                    self.downloader.log_message(f"分块 {chunk['id']} 修复后仍未完成")
                    repair_success = False
                    break
            except Exception as e:
                self.downloader.log_message(f"修复分块 {chunk['id']} 时发生异常: {e}")
                repair_success = False
                break

        if repair_success:
            self.downloader.log_message("所有需要修复的分块已成功下载")
            # 更新全局下载进度（已经由 _download_chunk 更新，但为了保险可重新计算）
            total_downloaded = sum(c['downloaded'] for c in self.chunks if c['completed'])
            self.downloaded_size = total_downloaded
        else:
            self.downloader.log_message("部分分块修复失败")

        return repair_success

    def _cleanup_temp_files(self, temp_dir):
        """删除临时分块文件和元数据文件"""
        try:
            # 删除所有分块文件
            for chunk in self.chunks:
                if os.path.exists(chunk['file']):
                    try:
                        os.remove(chunk['file'])
                    except Exception as e:
                        self.downloader.log_message(f"删除分块文件 {chunk['file']} 失败: {e}")

            # 删除元数据文件
            if self.chunk_meta_file and os.path.exists(self.chunk_meta_file):
                try:
                    os.remove(self.chunk_meta_file)
                except Exception as e:
                    self.downloader.log_message(f"删除元数据文件失败: {e}")

            # 删除临时目录（若为空）
            if os.path.exists(temp_dir):
                try:
                    os.rmdir(temp_dir)
                except OSError:
                    # 如果目录非空，记录警告
                    self.downloader.log_message(f"临时目录 {temp_dir} 非空，可能残留文件")
        except Exception as e:
            self.downloader.log_message(f"清理临时文件时发生错误: {e}")

    def _retry_merge(self, max_retries=3):
        """尝试重新合并分块 - 增强版本"""
        for attempt in range(max_retries):
            try:
                self.downloader.log_message(f"尝试重新合并分块 (尝试 {attempt+1}/{max_retries})")
                self._merge_chunks()
                return True
            except Exception as e:
                self.downloader.log_message(f"重新合并失败: {e}")
                time.sleep(1)  # 等待1秒再重试
        return False
    
    def _update_progress(self):
        """更新进度显示（使用瞬时速度）"""
        current_time = time.time()
        
        # 计算瞬时下载速度 (字节/秒)
        if self.last_update_time and self.last_downloaded is not None:
            time_diff = current_time - self.last_update_time
            if time_diff > 0:
                self.speed = (self.downloaded_size - self.last_downloaded) / time_diff
        else:
            self.speed = 0
        
        self.last_downloaded = self.downloaded_size
        self.last_update_time = current_time
        
        # 更新任务状态
        if self.total_size > 0:
            percent = (self.downloaded_size / self.total_size) * 100
            task_status = f"下载中 ({percent:.1f}%, {self.downloader.format_size(self.speed)}/s)"
            
            # 计算剩余时间 (秒)
            remaining_bytes = self.total_size - self.downloaded_size
            if self.speed > 0:
                remaining_time = remaining_bytes / self.speed
                time_info = f"剩余: {self.downloader.format_time(remaining_time)}"
            else:
                time_info = "计算中..."
        else:
            task_status = "下载中"
            time_info = "未知"
            
        # 更新大小信息
        if self.total_size > 0:
            size_info = f"{self.downloader.format_size(self.downloaded_size)} / {self.downloader.format_size(self.total_size)}"
        else:
            size_info = "未知大小"
            
        # 更新任务状态
        self.status = task_status
        self.size_info = size_info
        self.time_info = time_info
        
        # 更新UI（节流控制）
        if current_time - self.downloader.last_refresh_time >= self.downloader.refresh_interval:
            self.downloader.root.after(0, self.downloader.update_task_row, self)
            self.downloader.last_refresh_time = current_time

    def _download_complete(self):
        """下载完成处理"""
        # 确保下载大小等于总大小
        if self.downloaded_size < self.total_size:
            self.downloaded_size = self.total_size
            
        self.status = "已完成"
        self.is_completed = True
        self.size_info = f"{self.downloader.format_size(self.downloaded_size)} / {self.downloader.format_size(self.total_size)}"
        self.time_info = "完成"
        
        # 更新UI
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        
        # 下载完成后清除断点续传信息
        self.downloader.clear_resume_info(self.task_id)
        
        # 显示完成通知
        messagebox.showinfo("下载完成", f"文件下载完成: {os.path.basename(self.save_path)}")
        self.downloader.log_message(f"下载完成: {os.path.basename(self.save_path)}")
        
    def _handle_error(self, error_msg):
        """错误处理 - 增强错误分类"""
        # 增强错误分类处理
        if "网络错误" in error_msg or "ConnectionError" in error_msg:
            self.status = "网络错误: 请检查连接后重试"
        elif "Permission denied" in error_msg or "权限错误" in error_msg:
            self.status = f"权限错误: 无法访问 {os.path.basename(self.save_path)}"
        elif "No such file or directory" in error_msg:
            self.status = "路径错误: 目录不存在"
        elif "No connection adapters" in error_msg:
            self.status = "协议错误: 不支持的URL协议"
        elif "501" in error_msg:
            self.status = "服务器错误: 不支持的操作(501)"
        elif "404" in error_msg:
            self.status = "资源不存在(404)"
        elif "403" in error_msg:
            self.status = "访问被拒绝(403)"
        elif "Name or service not known" in error_msg:
            self.status = "DNS解析失败"
        else:
            # 截断过长的错误信息
            if len(error_msg) > 500:
                error_msg = error_msg[:500] + "..."
            self.status = f"错误: {error_msg}"
        
        # 关键修改：不再标记为完成状态
        self.size_info = "未知大小"
        self.time_info = "未知"
        self.is_downloading = False
        self.is_paused = False
        
        # 更新UI
        self.downloader.root.after(0, self.downloader.update_task_row, self)
        
        # 错误时清除断点续传信息（原有逻辑）
        self.downloader.clear_resume_info(self.task_id)
        
        # 记录日志（原有逻辑）
        self.downloader.log_message(f"下载失败: {self.url} - {error_msg}")


class PreConnectionManager:
    """预连接管理器"""
    def __init__(self, session):
        self.session = session
        self.connection_pool = {}  # 存储预建立的连接
        self.lock = threading.Lock()
        
    def pre_connect(self, url, max_connections=5):
        """预连接到服务器"""
        try:
            parsed = urlparse(url)
            hostname = parsed.hostname
            scheme = parsed.scheme
            
            if hostname not in self.connection_pool:
                self.connection_pool[hostname] = {
                    'connections': [],
                    'last_used': time.time(),
                    'scheme': scheme
                }
            
            # 预建立多个连接
            connections = []
            for i in range(max_connections):
                try:
                    # 创建预连接（发送HEAD请求建立连接）
                    headers = {'Range': 'bytes=0-100'}  # 小范围请求
                    response = self.session.head(url, headers=headers, timeout=10)
                    connections.append({
                        'response': response,
                        'established': time.time(),
                        'used': False
                    })
                except Exception as e:
                    print(f"预连接 {i+1} 失败: {e}")
                    continue
            
            with self.lock:
                self.connection_pool[hostname]['connections'].extend(connections)
                
            return len(connections)
        except Exception as e:
            print(f"预连接失败: {e}")
            return 0
    
    def get_connection(self, url):
        """获取预建立的连接"""
        parsed = urlparse(url)
        hostname = parsed.hostname
        
        if hostname not in self.connection_pool:
            return None
            
        with self.lock:
            connections = self.connection_pool[hostname]['connections']
            if not connections:
                return None
                
            # 找到未使用的连接
            for conn in connections:
                if not conn['used']:
                    conn['used'] = True
                    conn['last_used'] = time.time()
                    return conn
            
            # 所有连接都在使用，返回最早建立的连接
            oldest_conn = min(connections, key=lambda x: x['last_used'])
            oldest_conn['last_used'] = time.time()
            return oldest_conn
    
    def cleanup_old_connections(self, max_age=300):
        """清理过期的连接"""
        current_time = time.time()
        with self.lock:
            for hostname in list(self.connection_pool.keys()):
                connections = self.connection_pool[hostname]['connections']
                # 移除超过最大年龄的连接
                self.connection_pool[hostname]['connections'] = [
                    conn for conn in connections 
                    if current_time - conn['established'] < max_age
                ]
                
                # 如果该主机没有连接了，移除记录
                if not self.connection_pool[hostname]['connections']:
                    del self.connection_pool[hostname]

class DownloaderRequestHandler(BaseHTTPRequestHandler):
    """处理浏览器扩展发来的下载请求"""
    downloader_app = None   # 启动时注入 SmartDownloader 实例

    def do_GET(self):
        # 让扩展检测下载器是否运行
        if self.path == '/status':
            self.send_response(200)
            self.send_header('Content-type', 'text/plain')
            self.end_headers()
            self.wfile.write(b'ok')
            return
        # 其他 GET 请求一律 404
        self.send_response(404)
        self.end_headers()

    def do_POST(self):
        if self.path == '/add_task':
            content_length = int(self.headers.get('Content-Length', 0))
            post_data = self.rfile.read(content_length)
            try:
                data = json.loads(post_data)
                url = data.get('url', '').strip()
                filename = data.get('filename', '')
                headers = data.get('headers')
            except:
                url = ''
                filename = ''
                headers = None
            if url:
                # 通过 root.after 确保 UI 操作在主线程中执行
                self.downloader_app.root.after(0,lambda u=url, f=filename, h=headers: self._add_download(u, f, h))
                self.send_response(200)
                self.send_header('Content-type', 'application/json')
                self.end_headers()
                self.wfile.write(json.dumps({'status': 'ok'}).encode())
            else:
                self.send_response(400)
                self.end_headers()
        else:
            self.send_response(404)
            self.end_headers()

    def _add_download(self, url, filename, headers=None):
        app = self.downloader_app
        app.url_var.set(url)
        if filename:
            final_filename = os.path.basename(filename)
        else:
            final_filename = app.extract_filename(url)
        default_dir = getattr(app, 'default_dir_var', None)
        save_dir = default_dir.get() if (default_dir and default_dir.get()) else os.path.expanduser("~/Downloads")
        save_path = os.path.join(save_dir, final_filename)
        app.path_var.set(save_path)
        # 创建任务时传入 headers
        task = DownloadTask(url, save_path, app)
        if headers:
            task.custom_headers = headers 
        with app.lock:
            app.tasks.append(task)
        app.add_task_to_tree(task)
        if getattr(app, 'auto_start_var', None) and app.auto_start_var.get():
            app.start_download()
        else:
            app.log_message(f"已收到扩展推送链接，请手动开始下载：{url}")

    def log_message(self, format, *args):
        # 禁用 HTTP 服务器的日志输出，避免干扰主界面
        pass

class SmartDownloader:
    def __init__(self, root):
        self.root = root
        self.root.title("智能文件下载器")
        self.root.geometry("850x500")

        # 获取图标绝对路径
        icon_path = get_resource_path("d.ico")
        try:
            self.root.iconbitmap(icon_path)
        except Exception as e:
            print(f"图标加载错误: {e}")
            # 尝试替代方案
            self.root.iconbitmap(default="")  # 使用默认图标
        self.root.configure(bg="#f0f0f0")
        
        # 获取系统信息
        self.total_memory = psutil.virtual_memory().total
        self.max_threads = max(1, os.cpu_count() * 4)  # 使用4倍CPU核心数
        
        # 初始化变量
        self.url_var = tk.StringVar()
        self.path_var = tk.StringVar()
        self.thread_var = tk.IntVar(value=min(16, self.max_threads))  # 默认16线程
        self.cache_percent = tk.DoubleVar(value=10)  # 默认使用10%内存作为缓存
        self.tasks = []  # 存储所有下载任务
        self.lock = threading.Lock()  # 添加更新锁
        self.last_refresh_time = 0  # 上次刷新时间
        self.refresh_interval = 0.5  # 刷新间隔(秒)
        self.cache_var = tk.BooleanVar(value=True)
        self.max_cache_size = 0
        
        # 网络监控相关变量
        self.last_net_io = psutil.net_io_counters()
        self.last_net_time = time.time()
        self.net_speed_info = {"download": 0, "upload": 0}
        
        # 右键菜单变量
        self.context_menu = None
        self.selected_task = None

        # 创建连接池
        self.session = requests.Session()
        adapter = requests.adapters.HTTPAdapter(
            pool_connections=100,  # 最大连接数
            pool_maxsize=100,       # 最大连接池大小
            max_retries=3           # 自动重试
        )
        self.session.mount('http://', adapter)
        self.session.mount('https://', adapter)
        
        # 创建预连接管理器
        self.pre_connection_manager = PreConnectionManager(self.session)
        
        # 内存监控
        self.memory_usage = 0
        self.total_cached = 0
        
        # 网络超时配置（默认值）
        self.connect_timeout = 10
        self.read_timeout = 30
        
        # 默认启用校验
        self.verify_chunks = True

        # 设置UI
        self.setup_ui()
        
        # 加载保存的设置
        self.load_settings()
        
        # 加载断点续传信息
        self.load_resume_info()
        
        # 启动网络监控更新
        self.update_network_info()

        #调用监听服务
        self.start_http_listener()
        
        # 绑定关闭事件
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        
        # 启动自动线程调整
        self.root.after(10000, self.adjust_thread_count)

        # 创建底部状态栏
        self.create_status_bar()
        
    def create_status_bar(self):
        """创建底部状态栏"""
        # 修复：使用 self.root 代替 root
        bottom_frame = tk.Frame(self.root, bg="#f0f0f0", height=20)
        bottom_frame.pack(side=tk.BOTTOM, fill=tk.X)
        
        # 添加协议提示和版本号
        agreement_label = tk.Label(
            bottom_frame, 
            text="协议提示 版本号1.15.0 | 制作者AF",
            bg="#f0f0f0",
            fg="#666666",
            font=("Arial", 9)
        )
        agreement_label.pack(side=tk.RIGHT, padx=10, pady=2)
        
    def adjust_thread_count(self):
        """根据下载速度自动调整线程数"""
        if len(self.tasks) == 0:
            # 没有任务，10秒后再检查
            self.root.after(10000, self.adjust_thread_count)
            return
            
        # 计算平均下载速度
        active_tasks = [t for t in self.tasks if t.is_downloading and not t.is_paused]
        if not active_tasks:
            self.root.after(10000, self.adjust_thread_count)
            return
            
        total_speed = sum(t.speed for t in active_tasks)
        
        # 动态调整线程数 (8-100线程范围)
        current_threads = self.thread_var.get()
        if total_speed < 1024 * 1024:  # <1MB/s
            new_count = min(50, max(8, current_threads - 2))
        elif total_speed < 10 * 1024 * 1024:  # <10MB/s
            new_count = min(80, max(16, current_threads + 2))
        else:  # >10MB/s
            new_count = min(100, max(24, current_threads + 4))
        
        if new_count != current_threads:
            self.thread_var.set(new_count)
            self.log_message(f"自动调整线程数: {current_threads} -> {new_count}")
        
        # 10秒后再次调整
        self.root.after(10000, self.adjust_thread_count)
    
    def setup_ui(self):
        # 创建标签页
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # 第一页：下载链接和保存位置
        self.page1 = ttk.Frame(self.notebook)
        self.notebook.add(self.page1, text="下载")
        
        # 第二页：下载任务列表
        self.page2 = ttk.Frame(self.notebook)
        self.notebook.add(self.page2, text="任务")
        
        # 第三页：系统信息
        self.page3 = ttk.Frame(self.notebook)
        self.notebook.add(self.page3, text="系统")

        # 第四页: 设置页
        self.page4 = ttk.Frame(self.notebook) 
        self.notebook.add(self.page4, text="设置")
        
        # 在第一页设置UI
        self.setup_page1()
        
        # 在第二页设置UI
        self.setup_page2()
        
        # 在第三页设置UI
        self.setup_page3()
        
        # 在第四页设置UI
        self.setup_page4()

        # 添加协议提示
        protocol_frame = tk.Frame(self.page1, bg="#f0f0f0")
        protocol_frame.grid(row=5, column=0, columnspan=3, padx=10, pady=5, sticky=tk.W)
        
        tk.Label(protocol_frame, 
                text="支持的协议: HTTP, HTTPS, FTP, file://, blob:",
                bg="#f0f0f0", font=('微软雅黑', 8), fg="#666666").pack(side=tk.LEFT)
    
    def setup_page1(self):
        # 样式配置
        self.page1.columnconfigure(1, weight=1)
        
        # 第一行：URL输入
        url_frame = tk.Frame(self.page1, bg="#f0f0f0")
        url_frame.grid(row=0, column=0, columnspan=3, padx=10, pady=10, sticky=tk.EW)
        
        tk.Label(url_frame, text="下载链接:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        
        # 输入框和清除按钮容器
        entry_clear_frame = tk.Frame(url_frame, bg="#f0f0f0")
        entry_clear_frame.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 0))
        
        # URL输入框
        self.url_entry = tk.Entry(entry_clear_frame, textvariable=self.url_var, 
                                font=('微软雅黑', 10), bd=2)
        self.url_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.url_entry.bind('<KeyRelease>', self.on_url_change)

        # 清除按钮
        clear_btn = tk.Button(entry_clear_frame, text="X", 
                            command=self.clear_url, 
                            bg="#ff4444", fg="white", 
                            width=2, height=1, 
                            font=('Arial', 10, 'bold'))
        clear_btn.pack(side=tk.LEFT, padx=(2, 0))

        # 第二行：保存位置和按钮
        path_frame = tk.Frame(self.page1, bg="#f0f0f0")
        path_frame.grid(row=1, column=0, columnspan=3, padx=10, pady=10, sticky=tk.EW)
        
        tk.Label(path_frame, text="保存位置:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        
        self.path_entry = tk.Entry(path_frame, textvariable=self.path_var, 
                                 font=('微软雅黑', 10), bd=2)
        self.path_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(5, 0))

        btn_frame = tk.Frame(path_frame, bg="#f0f0f0")
        btn_frame.pack(side=tk.LEFT, padx=(5, 0))
        
        tk.Button(btn_frame, text="浏览", command=self.browse_path,
                 bg="#4a7abc", fg="white", font=('微软雅黑', 9)).pack(side=tk.LEFT, padx=2)
        
        self.download_btn = tk.Button(btn_frame, text="开始下载", 
                                    command=self.start_download,
                                    bg="#4CAF50", fg="white", 
                                    font=('微软雅黑', 9, 'bold'))
        self.download_btn.pack(side=tk.LEFT, padx=2)
        
        # 添加线程数选择
        thread_frame = tk.Frame(self.page1, bg="#f0f0f0")
        thread_frame.grid(row=2, column=0, columnspan=3, padx=10, pady=5, sticky=tk.EW)
        
        tk.Label(thread_frame, text="线程数:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        
        # 自定义线程输入框
        def validate_thread(new_value):
            if new_value == "":
                return True
            try:
                value = int(new_value)
                if 1 <= value <= min(100, self.max_threads):
                    return True
            except ValueError:
                pass
            return False
        
        vcmd = (thread_frame.register(validate_thread), '%P')
        thread_entry = tk.Entry(thread_frame, textvariable=self.thread_var, 
                              validate="key", validatecommand=vcmd,
                              font=('微软雅黑', 10), width=5)
        thread_entry.pack(side=tk.LEFT, padx=5)
        
        # 添加最大线程数提示
        max_thread_info = tk.Label(thread_frame, 
                                  text=f"(最大推荐: {self.max_threads})",
                                  bg="#f0f0f0", font=('微软雅黑', 9), fg="#666666")
        max_thread_info.pack(side=tk.LEFT, padx=5)
        
        # 添加缓存选项
        cache_frame = tk.Frame(self.page1, bg="#f0f0f0")
        cache_frame.grid(row=3, column=0, columnspan=3, padx=9, pady=5, sticky=tk.EW)
        
        cache_check = tk.Checkbutton(cache_frame, text="启用内存缓存", variable=self.cache_var,
                                    bg="#f0f0f0", font=('微软雅黑', 10))
        cache_check.pack(side=tk.LEFT)
        
        # 内存缓存设置（默认隐藏）
        self.cache_settings_frame = tk.Frame(self.page1, bg="#f0f0f0")
        self.cache_settings_frame.grid(row=4, column=0, columnspan=3, padx=10, pady=5, sticky=tk.EW)
        
        tk.Label(self.cache_settings_frame, text="内存缓存:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        
        # 百分比滑块
        self.cache_percent_scale = tk.Scale(self.cache_settings_frame, variable=self.cache_percent, 
                                     from_=0, to=50, orient=tk.HORIZONTAL, 
                                     resolution=1, showvalue=True, length=400, 
                                     bg="#f0f0f0", font=('微软雅黑', 9))
        self.cache_percent_scale.pack(side=tk.LEFT, padx=9)
        
        # 显示当前设置的内存大小
        def update_cache_label(*args):
            percent = self.cache_percent.get()
            cache_size = self.total_memory * percent / 100
            self.max_cache_size = cache_size
            if hasattr(self, 'cache_size_label'):
                self.cache_size_label.config(text=f"最大缓存: {self.format_size(cache_size)} ({percent:.0f}%)")
        
        self.cache_percent.trace_add("write", update_cache_label)
        
        self.cache_size_label = tk.Label(self.cache_settings_frame, 
                                       text=f"最大缓存: {self.format_size(0)} (0%)", 
                                       bg="#f0f0f0", font=('微软雅黑', 9))
        self.cache_size_label.pack(side=tk.LEFT, padx=5)
        
        # 根据cache_var状态显示/隐藏缓存设置
        def toggle_cache_settings(*args):
            if self.cache_var.get():
                # 显示缓存设置
                self.cache_settings_frame.grid()
                update_cache_label()
            else:
                # 隐藏缓存设置
                self.cache_settings_frame.grid_remove()
                self.max_cache_size = 0
                if hasattr(self, 'cache_size_label'):
                    self.cache_size_label.config(text=f"最大缓存: {self.format_size(0)} (0%)")
        
        self.cache_var.trace_add("write", toggle_cache_settings)
        
        # 初始化：根据默认值显示/隐藏
        toggle_cache_settings()
        
    def setup_page2(self):
        # 创建Treeview显示下载任务
        columns = ("url", "status", "progress", "size", "time", "cache", "action")
        self.task_tree = ttk.Treeview(self.page2, columns=columns, show="headings")
        
        # 设置列标题
        self.task_tree.heading("url", text="下载链接")
        self.task_tree.heading("status", text="状态")
        self.task_tree.heading("progress", text="进度")
        self.task_tree.heading("size", text="大小")
        self.task_tree.heading("time", text="剩余时间")
        self.task_tree.heading("cache", text="缓存使用")
        self.task_tree.heading("action", text="操作")
        
        # 设置列宽
        self.task_tree.column("url", width=130)
        self.task_tree.column("status", width=130)
        self.task_tree.column("progress", width=80)
        self.task_tree.column("size", width=120)
        self.task_tree.column("time", width=100)
        self.task_tree.column("cache", width=100)
        self.task_tree.column("action", width=120)  # 加宽操作列
        
        # 绑定点击事件
        self.task_tree.bind("<Button-1>", self.on_tree_click)
        # 绑定右键点击事件
        self.task_tree.bind("<Button-3>", self.on_tree_right_click)
        
        scrollbar = ttk.Scrollbar(self.page2, orient=tk.VERTICAL, command=self.task_tree.yview)
        self.task_tree.configure(yscrollcommand=scrollbar.set)
        
        # 使用grid布局
        self.task_tree.grid(row=0, column=0, sticky=tk.NSEW, padx=10, pady=10)
        scrollbar.grid(row=0, column=1, sticky=tk.NS, pady=10)
        
        # 创建按钮容器
        button_frame = tk.Frame(self.page2)
        button_frame.grid(row=1, column=0, columnspan=2, sticky=tk.EW, padx=10, pady=5)
        
        # 配置网格行列权重
        self.page2.grid_rowconfigure(0, weight=1)  # Treeview行权重为1
        self.page2.grid_columnconfigure(0, weight=1)  # 主列权重为1
        self.page2.grid_columnconfigure(1, weight=0)  # 滚动条列权重为0
        
        # 创建按钮
        buttons = [
            ("刷新任务列表", self.refresh_task_list, "#2196F3"),
            ("删除选中任务", self.delete_selected_task, "#F44336"),
            ("删除所有任务", self.delete_all_tasks, "#FF5722"),
            ("一键停止", self.stop_all_tasks, "#FF9800"),
            ("一键开始", self.start_all_tasks, "#4CAF50"),
        ]
        
        for text, command, color in buttons:
            btn = tk.Button(button_frame, text=text, command=command,
                          bg=color, fg="white", font=('微软雅黑', 10))
            btn.pack(side=tk.LEFT, expand=True, fill=tk.X, padx=2)
        
        # 配置按钮容器的权重
        button_frame.columnconfigure(tuple(range(len(buttons))), weight=1)
        
        # 创建右键菜单
        self.context_menu = tk.Menu(self.root, tearoff=0)
        self.context_menu.add_command(label="复制下载链接", command=self.copy_download_url)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="暂停/继续任务", command=self.toggle_task_pause)
        self.context_menu.add_command(label="删除任务", command=self.delete_selected_context_task)
        
        # 初始化选中的任务
        self.selected_task = None
        
    def setup_page3(self):
        # 创建内存监控区域
        mem_frame = tk.LabelFrame(self.page3, text="内存使用情况", bg="#f0f0f0")
        mem_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 内存使用标签
        self.mem_info = tk.Label(mem_frame, bg="#f0f0f0", font=('微软雅黑', 9), justify=tk.LEFT)
        self.mem_info.pack(padx=10, pady=5)
        
        # 创建网络监控区域
        net_frame = tk.LabelFrame(self.page3, text="网络吞吐量", bg="#f0f0f0")
        net_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 创建一行显示网络速度
        net_speed_frame = tk.Frame(net_frame, bg="#f0f0f0")
        net_speed_frame.pack(padx=10, pady=5, fill=tk.X)
        
        # 下载速度标签
        self.download_speed_label = tk.Label(net_speed_frame, 
                                            text="下载速度: 0 KB/s", 
                                            bg="#f0f0f0", font=('微软雅黑', 10))
        self.download_speed_label.pack(side=tk.LEFT, padx=(0, 20))
        
        # 上传速度标签
        self.upload_speed_label = tk.Label(net_speed_frame, 
                                          text="上传速度: 0 KB/s", 
                                          bg="#f0f0f0", font=('微软雅黑', 10))
        self.upload_speed_label.pack(side=tk.LEFT)
        
        # 日志区域
        log_frame = tk.LabelFrame(self.page3, text="系统日志", bg="#f0f0f0")
        log_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        self.log_text = scrolledtext.ScrolledText(log_frame, height=10, 
                                                 font=('微软雅黑', 8), bg="#fff", fg="#333")
        self.log_text.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        self.log_text.config(state=tk.DISABLED)
        
        # 启动内存监控更新
        self.update_memory_info()
        
    def setup_page4(self):
        """设置页面配置"""
        # 创建滚动区域
        canvas = tk.Canvas(self.page4, bg="#f0f0f0", highlightthickness=0)
        scrollbar = ttk.Scrollbar(self.page4, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # 绑定鼠标滚轮事件
        def _on_mousewheel(event):
            canvas.yview_scroll(int(-1*(event.delta/120)), "units")
        
        canvas.bind_all("<MouseWheel>", _on_mousewheel)
        
        # 布局
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        
        # ========== 下载设置 ==========
        download_frame = tk.LabelFrame(scrollable_frame, text="下载设置", bg="#f0f0f0", padx=10, pady=10)
        download_frame.pack(fill=tk.X, padx=10, pady=10, anchor=tk.NW)
        
        # 1. 默认线程数
        thread_frame = tk.Frame(download_frame, bg="#f0f0f0")
        thread_frame.pack(fill=tk.X, pady=5)
        tk.Label(thread_frame, text="默认线程数:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.default_threads = tk.IntVar(value=self.thread_var.get())
        tk.Spinbox(thread_frame, from_=1, to=100, textvariable=self.default_threads, 
                width=10, font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=10)
        
        # 2. 默认下载目录
        default_dir_frame = tk.Frame(download_frame, bg="#f0f0f0")
        default_dir_frame.pack(fill=tk.X, pady=5)
        tk.Label(default_dir_frame, text="默认下载目录:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.default_dir_var = tk.StringVar(value=os.path.expanduser("~/Downloads"))
        default_dir_entry = tk.Entry(default_dir_frame, textvariable=self.default_dir_var, 
                                    font=('微软雅黑', 10), width=40)
        default_dir_entry.pack(side=tk.LEFT, padx=10)
        tk.Button(default_dir_frame, text="浏览", command=self.browse_default_dir,
                bg="#4a7abc", fg="white", font=('微软雅黑', 9)).pack(side=tk.LEFT)
        
        # 3. 自动开始下载
        self.auto_start_var = tk.BooleanVar(value=True)
        tk.Checkbutton(download_frame, text="添加任务后自动开始下载", 
                    variable=self.auto_start_var, bg="#f0f0f0", 
                    font=('微软雅黑', 10)).pack(anchor=tk.W, pady=5)
        
        # 4. 下载完成后提示
        self.completion_notify_var = tk.BooleanVar(value=True)
        tk.Checkbutton(download_frame, text="下载完成后显示提示", 
                    variable=self.completion_notify_var, bg="#f0f0f0", 
                    font=('微软雅黑', 10)).pack(anchor=tk.W, pady=5)
        
        # 5. 下载速度限制
        speed_limit_frame = tk.Frame(download_frame, bg="#f0f0f0")
        speed_limit_frame.pack(fill=tk.X, pady=5)
        tk.Label(speed_limit_frame, text="下载速度限制:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.speed_limit_var = tk.IntVar(value=0)  # 0表示无限制
        tk.Spinbox(speed_limit_frame, from_=0, to=100000, increment=100, 
                textvariable=self.speed_limit_var, width=10, font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=10)
        tk.Label(speed_limit_frame, text="KB/s (0为无限制)", bg="#f0f0f0", 
                font=('微软雅黑', 9), fg="#666666").pack(side=tk.LEFT)
        
        # ========== 网络设置 ==========
        network_frame = tk.LabelFrame(scrollable_frame, text="网络设置", bg="#f0f0f0", padx=10, pady=10)
        network_frame.pack(fill=tk.X, padx=10, pady=10, anchor=tk.NW)
        
        # 1. 超时设置
        timeout_frame = tk.Frame(network_frame, bg="#f0f0f0")
        timeout_frame.pack(fill=tk.X, pady=5)
        tk.Label(timeout_frame, text="连接超时:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.connect_timeout_var = tk.IntVar(value=10)
        tk.Spinbox(timeout_frame, from_=1, to=60, textvariable=self.connect_timeout_var, 
                width=8, font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=5)
        tk.Label(timeout_frame, text="秒", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        
        tk.Label(timeout_frame, text="读取超时:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(20,0))
        self.read_timeout_var = tk.IntVar(value=30)
        tk.Spinbox(timeout_frame, from_=5, to=300, textvariable=self.read_timeout_var, 
                width=8, font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=5)
        tk.Label(timeout_frame, text="秒", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        
        # 2. 重试次数
        retry_frame = tk.Frame(network_frame, bg="#f0f0f0")
        retry_frame.pack(fill=tk.X, pady=5)
        tk.Label(retry_frame, text="失败重试次数:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.retry_count_var = tk.IntVar(value=3)
        tk.Spinbox(retry_frame, from_=0, to=10, textvariable=self.retry_count_var, 
                width=8, font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=10)
        
        # 3. 代理设置
        proxy_frame = tk.Frame(network_frame, bg="#f0f0f0")
        proxy_frame.pack(fill=tk.X, pady=5)
        tk.Label(proxy_frame, text="代理服务器:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.proxy_var = tk.StringVar(value="")
        tk.Entry(proxy_frame, textvariable=self.proxy_var, font=('微软雅黑', 10), 
                width=40).pack(side=tk.LEFT, padx=10)
        
        # ========== 界面设置 ==========
        ui_frame = tk.LabelFrame(scrollable_frame, text="界面设置", bg="#f0f0f0", padx=10, pady=10)
        ui_frame.pack(fill=tk.X, padx=10, pady=10, anchor=tk.NW)
        
        # 1. 界面主题
        theme_frame = tk.Frame(ui_frame, bg="#f0f0f0")
        theme_frame.pack(fill=tk.X, pady=5)
        tk.Label(theme_frame, text="界面主题:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.theme_var = tk.StringVar(value="default")
        themes = ["default", "light", "dark", "blue"]
        theme_combo = ttk.Combobox(theme_frame, textvariable=self.theme_var, 
                                values=themes, state="readonly", width=15)
        theme_combo.pack(side=tk.LEFT, padx=10)
        
        # 2. 字体大小
        font_frame = tk.Frame(ui_frame, bg="#f0f0f0")
        font_frame.pack(fill=tk.X, pady=5)
        tk.Label(font_frame, text="字体大小:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.font_size_var = tk.IntVar(value=10)
        tk.Scale(font_frame, variable=self.font_size_var, from_=8, to=16, 
                orient=tk.HORIZONTAL, length=200, showvalue=False).pack(side=tk.LEFT, padx=10)
        self.font_size_label = tk.Label(font_frame, textvariable=self.font_size_var, bg="#f0f0f0", 
                font=('微软雅黑', 10))
        self.font_size_label.pack(side=tk.LEFT)
        
        # 3. 刷新频率
        refresh_frame = tk.Frame(ui_frame, bg="#f0f0f0")
        refresh_frame.pack(fill=tk.X, pady=5)
        tk.Label(refresh_frame, text="界面刷新频率:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.refresh_interval_var = tk.DoubleVar(value=self.refresh_interval)
        tk.Scale(refresh_frame, variable=self.refresh_interval_var, from_=0.1, to=2.0, 
                resolution=0.1, orient=tk.HORIZONTAL, length=200, showvalue=False).pack(side=tk.LEFT, padx=10)
        self.refresh_interval_label = tk.Label(refresh_frame, text=f"{self.refresh_interval_var.get():.1f}秒", bg="#f0f0f0", 
                font=('微软雅黑', 10))
        self.refresh_interval_label.pack(side=tk.LEFT)
        self.refresh_interval_var.trace_add("write", self.update_refresh_interval)
        
        # 4. 显示设置
        self.show_speed_var = tk.BooleanVar(value=True)
        tk.Checkbutton(ui_frame, text="在任务列表显示实时速度", 
                    variable=self.show_speed_var, bg="#f0f0f0", 
                    font=('微软雅黑', 10)).pack(anchor=tk.W, pady=5)
        
        self.show_progress_bar_var = tk.BooleanVar(value=True)
        tk.Checkbutton(ui_frame, text="显示进度条", 
                    variable=self.show_progress_bar_var, bg="#f0f0f0", 
                    font=('微软雅黑', 10)).pack(anchor=tk.W, pady=5)
        
        # ========== 高级设置 ==========
        advanced_frame = tk.LabelFrame(scrollable_frame, text="高级设置", bg="#f0f0f0", padx=10, pady=10)
        advanced_frame.pack(fill=tk.X, padx=10, pady=10, anchor=tk.NW)
        
        # ----- 新增：分块完整性校验 -----
        self.verify_chunks_var = tk.BooleanVar(value=True)
        tk.Checkbutton(advanced_frame, text="启用分块完整性校验 (SHA-256)", 
                    variable=self.verify_chunks_var, bg="#f0f0f0", 
                    font=('微软雅黑', 10)).pack(anchor=tk.W, pady=5)
        
        # 1. 内存缓存设置
        cache_frame = tk.Frame(advanced_frame, bg="#f0f0f0")
        cache_frame.pack(fill=tk.X, pady=5)
        tk.Checkbutton(cache_frame, text="启用内存缓存", variable=self.cache_var,
                    bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        
        # 缓存大小设置（放在单独的frame中，以便显示/隐藏）
        self.settings_cache_controls = tk.Frame(cache_frame, bg="#f0f0f0")
        tk.Label(self.settings_cache_controls, text="缓存大小:", bg="#f0f0f0", 
                font=('微软雅黑', 10)).pack(side=tk.LEFT, padx=(0,5))
        tk.Scale(self.settings_cache_controls, variable=self.cache_percent, from_=0, to=50, 
                orient=tk.HORIZONTAL, length=200, showvalue=False).pack(side=tk.LEFT)
        self.cache_percent_label = tk.Label(self.settings_cache_controls, text=f"{self.cache_percent.get():.0f}%", bg="#f0f0f0", 
                font=('微软雅黑', 10))
        self.cache_percent_label.pack(side=tk.LEFT, padx=5)
        def toggle_cache_settings_in_settings(*args):
            if self.cache_var.get():
                self.settings_cache_controls.pack(side=tk.LEFT, padx=(20,0))
            else:
                self.settings_cache_controls.pack_forget()
        self.cache_var.trace_add("write", toggle_cache_settings_in_settings)
        toggle_cache_settings_in_settings()  # 初始化时执行一次
        
        # 同步更新百分比标签和缓存大小
        self.cache_percent.trace_add("write", self.update_cache_from_settings)
        
        # 2. 分块大小
        chunk_frame = tk.Frame(advanced_frame, bg="#f0f0f0")
        chunk_frame.pack(fill=tk.X, pady=5)
        tk.Label(chunk_frame, text="分块大小:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.chunk_size_var = tk.StringVar(value="auto")
        chunk_sizes = ["auto", "1MB", "4MB", "8MB", "16MB", "32MB"]
        chunk_combo = ttk.Combobox(chunk_frame, textvariable=self.chunk_size_var, 
                                values=chunk_sizes, state="readonly", width=10)
        chunk_combo.pack(side=tk.LEFT, padx=10)
        
        # 3. 日志级别
        log_frame = tk.Frame(advanced_frame, bg="#f0f0f0")
        log_frame.pack(fill=tk.X, pady=5)
        tk.Label(log_frame, text="日志级别:", bg="#f0f0f0", font=('微软雅黑', 10)).pack(side=tk.LEFT)
        self.log_level_var = tk.StringVar(value="INFO")
        log_levels = ["DEBUG", "INFO", "WARNING", "ERROR"]
        log_combo = ttk.Combobox(log_frame, textvariable=self.log_level_var, 
                                values=log_levels, state="readonly", width=10)
        log_combo.pack(side=tk.LEFT, padx=10)
        
        # ========== 保存/重置按钮 ==========
        button_frame = tk.Frame(scrollable_frame, bg="#f0f0f0")
        button_frame.pack(fill=tk.X, padx=10, pady=20)
        
        tk.Button(button_frame, text="保存设置", command=self.save_settings,
                bg="#4CAF50", fg="white", font=('微软雅黑', 11, 'bold'),
                width=15).pack(side=tk.LEFT, padx=5)
        
        tk.Button(button_frame, text="恢复默认", command=self.reset_settings,
                bg="#FF9800", fg="white", font=('微软雅黑', 11),
                width=15).pack(side=tk.LEFT, padx=5)
        
        tk.Button(button_frame, text="立即应用", command=self.apply_settings,
                bg="#2196F3", fg="white", font=('微软雅黑', 11),
                width=15).pack(side=tk.LEFT, padx=5)

    def apply_settings(self):
        """立即应用所有设置到当前实例"""
        try:
            # 1. 应用下载设置
            # 更新主界面线程数显示（仅更新变量，新建任务时会读取）
            self.thread_var.set(min(self.default_threads.get(), self.max_threads))
            
            # 2. 应用网络设置
            proxy = self.proxy_var.get().strip()
            if proxy:
                # 验证代理格式
                if not (proxy.startswith('http://') or proxy.startswith('https://') or proxy.startswith('socks5://')):
                    proxy = 'http://' + proxy
                self.session.proxies = {'http': proxy, 'https': proxy}
                self.log_message(f"已设置代理: {proxy}")
            else:
                self.session.proxies = {}
                self.log_message("已清除代理设置")
            
            # 更新会话超时配置
            self.connect_timeout = self.connect_timeout_var.get()
            self.read_timeout = self.read_timeout_var.get()
            self.log_message(f"已更新超时设置: 连接={self.connect_timeout}秒, 读取={self.read_timeout}秒")
            
            # 3. 应用高级设置到现有任务（如果任务正在运行）
            new_chunk_size_setting = self.chunk_size_var.get()
            # 将设置值转换为字节数，供 DownloadTask 使用
            chunk_size_map = {
                "auto": None,  # None 表示由 DownloadTask 自动判断
                "1MB": 1024 * 1024,
                "4MB": 1024 * 1024 * 4,
                "8MB": 1024 * 1024 * 8,
                "16MB": 1024 * 1024 * 16,
                "32MB": 1024 * 1024 * 32,
            }
            self.chunk_size_setting = chunk_size_map.get(new_chunk_size_setting, None)
            
            # 应用缓存设置
            cache_percent = self.cache_percent.get()
            self.max_cache_size = self.total_memory * cache_percent / 100
            self.log_message(f"已更新缓存设置: {cache_percent:.0f}% ({self.format_size(self.max_cache_size)})")
            
            # 4. 应用界面设置
            # 更新刷新间隔
            self.refresh_interval = self.refresh_interval_var.get()
            
            # 尝试应用主题（示例，实际需要更复杂的主题引擎）
            self.apply_theme(self.theme_var.get())
            
            # 应用字体大小
            font_size = self.font_size_var.get()
            self.apply_font_size(font_size)
            self.log_message(f"字体大小设置为: {font_size}")
            
            # 5. 应用日志级别
            log_level = self.log_level_var.get()
            # 这里可以集成Python的logging模块，此处仅作演示
            self.log_message(f"日志级别设置为: {log_level}")
            
            # 6.应用分块完整性校验
            self.verify_chunks = self.verify_chunks_var.get()
            self.log_message(f"分块完整性校验: {'启用' if self.verify_chunks else '禁用'}")

            # 提示用户部分设置需要重启新任务生效
            messagebox.showinfo("应用成功", 
                            "网络、界面、缓存设置已立即生效。\n"
                            "线程数、分块大小等下载参数将在新建任务时应用。")
            self.log_message("所有设置已应用")
            
        except Exception as e:
            messagebox.showerror("应用失败", f"应用设置时出错: {str(e)}")
            self.log_message(f"应用设置失败: {e}")

    def browse_default_dir(self):
        """浏览选择默认下载目录"""
        directory = filedialog.askdirectory(
            title="选择默认下载目录",
            initialdir=self.default_dir_var.get()
        )
        if directory:
            self.default_dir_var.set(directory)

    def update_refresh_interval(self, *args):
        """更新刷新频率显示"""
        self.refresh_interval = self.refresh_interval_var.get()
        self.refresh_interval_label.config(text=f"{self.refresh_interval:.1f}秒")
    
    def update_cache_from_settings(self, *args):
        """从设置页面更新缓存大小（同时更新max_cache_size和Label）"""
        percent = self.cache_percent.get()
        # 计算最大缓存大小
        self.max_cache_size = self.total_memory * percent / 100
        # 更新设置页面的Label显示
        if hasattr(self, 'cache_percent_label'):
            self.cache_percent_label.config(text=f"{percent:.0f}%")
        # 如果下载栏的cache_size_label存在，也更新它
        if hasattr(self, 'cache_size_label'):
            self.cache_size_label.config(text=f"最大缓存: {self.format_size(self.max_cache_size)} ({percent:.0f}%)")
    
    def update_cache_percent(self, *args):
        """更新缓存百分比显示（仅用于设置页面Label）"""
        if hasattr(self, 'cache_percent_label'):
            self.cache_percent_label.config(text=f"{self.cache_percent.get():.0f}%")

    def save_settings(self):
        """保存设置到文件"""
        settings = {
            "download": {
                "default_threads": self.default_threads.get(),
                "default_dir": self.default_dir_var.get(),
                "auto_start": self.auto_start_var.get(),
                "completion_notify": self.completion_notify_var.get(),
                "speed_limit": self.speed_limit_var.get()
            },
            "network": {
                "connect_timeout": self.connect_timeout_var.get(),
                "read_timeout": self.read_timeout_var.get(),
                "retry_count": self.retry_count_var.get(),
                "proxy": self.proxy_var.get()
            },
            "ui": {
                "theme": self.theme_var.get(),
                "font_size": self.font_size_var.get(),
                "refresh_interval": self.refresh_interval_var.get(),
                "show_speed": self.show_speed_var.get(),
                "show_progress_bar": self.show_progress_bar_var.get()
            },
            "advanced": {
                "enable_cache": self.cache_var.get(),
                "cache_percent": self.cache_percent.get(),
                "chunk_size": self.chunk_size_var.get(),
                "log_level": self.log_level_var.get(),
                "verify_chunks": self.verify_chunks_var.get()
            }
        }
        
        try:
            with open("downloader_settings.json", "w", encoding="utf-8") as f:
                json.dump(settings, f, indent=4, ensure_ascii=False)
            messagebox.showinfo("保存成功", "设置已保存到 downloader_settings.json")
            self.log_message("设置保存成功")
        except Exception as e:
            messagebox.showerror("保存失败", f"保存设置失败: {str(e)}")
            self.log_message(f"保存设置失败: {e}")

    def load_settings(self):
        """从文件加载设置（已修复 trace_info 错误）"""
        try:
            if os.path.exists("downloader_settings.json"):
                with open("downloader_settings.json", "r", encoding="utf-8") as f:
                    settings = json.load(f)
                
                # 应用下载设置
                download = settings.get("download", {})
                self.default_threads.set(download.get("default_threads", 16))
                self.default_dir_var.set(download.get("default_dir", os.path.expanduser("~/Downloads")))
                self.auto_start_var.set(download.get("auto_start", True))
                self.completion_notify_var.set(download.get("completion_notify", True))
                self.speed_limit_var.set(download.get("speed_limit", 0))
                
                # 应用网络设置
                network = settings.get("network", {})
                self.connect_timeout_var.set(network.get("connect_timeout", 10))
                self.read_timeout_var.set(network.get("read_timeout", 30))
                self.retry_count_var.set(network.get("retry_count", 3))
                self.proxy_var.set(network.get("proxy", ""))
                
                # 应用超时配置
                self.connect_timeout = network.get("connect_timeout", 10)
                self.read_timeout = network.get("read_timeout", 30)
                
                # 应用代理设置到session
                proxy = network.get("proxy", "").strip()
                if proxy:
                    if not (proxy.startswith('http://') or proxy.startswith('https://') or proxy.startswith('socks5://')):
                        proxy = 'http://' + proxy
                    self.session.proxies = {'http': proxy, 'https': proxy}
                    self.log_message(f"已加载代理设置: {proxy}")
                else:
                    self.session.proxies = {}
                
                # 应用界面设置
                ui = settings.get("ui", {})
                self.theme_var.set(ui.get("theme", "default"))
                self.font_size_var.set(ui.get("font_size", 10))
                self.refresh_interval_var.set(ui.get("refresh_interval", 0.5))
                self.show_speed_var.set(ui.get("show_speed", True))
                self.show_progress_bar_var.set(ui.get("show_progress_bar", True))
                
                # 应用高级设置
                advanced = settings.get("advanced", {})
                self.cache_var.set(advanced.get("enable_cache", True))
                self.cache_percent.set(advanced.get("cache_percent", 10))
                self.chunk_size_var.set(advanced.get("chunk_size", "auto"))
                self.log_level_var.set(advanced.get("log_level", "INFO"))
                self.verify_chunks_var.set(advanced.get("verify_chunks", True))
                self.verify_chunks = self.verify_chunks_var.get()

                # 手动更新Label显示和缓存大小
                if hasattr(self, 'refresh_interval_label'):
                    self.refresh_interval_label.config(text=f"{self.refresh_interval_var.get():.1f}秒")
                if hasattr(self, 'cache_percent_label'):
                    self.cache_percent_label.config(text=f"{self.cache_percent.get():.0f}%")
                # 更新max_cache_size
                cache_pct = self.cache_percent.get()
                self.max_cache_size = self.total_memory * cache_pct / 100
                if hasattr(self, 'cache_size_label'):
                    self.cache_size_label.config(text=f"最大缓存: {self.format_size(self.max_cache_size)} ({cache_pct:.0f}%)")
                
                # 应用字体大小
                font_size = self.font_size_var.get()
                self.apply_font_size(font_size)
                
                self.log_message("设置加载成功")
        except Exception as e:
            self.log_message(f"加载设置失败: {e}")

    def reset_settings(self):
        """恢复默认设置"""
        if messagebox.askyesno("确认重置", "确定要恢复所有默认设置吗？"):
            # 下载设置
            self.default_threads.set(16)
            self.default_dir_var.set(os.path.expanduser("~/Downloads"))
            self.auto_start_var.set(True)
            self.completion_notify_var.set(True)
            self.speed_limit_var.set(0)
            
            # 网络设置
            self.connect_timeout_var.set(10)
            self.read_timeout_var.set(30)
            self.retry_count_var.set(3)
            self.proxy_var.set("")
            self.session.proxies = {}  # 清除代理设置
            self.connect_timeout = 10  # 重置超时配置
            self.read_timeout = 30
            
            # 界面设置
            self.theme_var.set("default")
            self.font_size_var.set(10)
            self.refresh_interval_var.set(0.5)
            self.show_speed_var.set(True)
            self.show_progress_bar_var.set(True)
            
            # 高级设置
            self.cache_var.set(True)
            self.cache_percent.set(10)
            self.chunk_size_var.set("auto")
            self.log_level_var.set("INFO")
            self.verify_chunks_var.set(True)
            
            # 更新缓存大小
            self.max_cache_size = self.total_memory * 10 / 100
            if hasattr(self, 'cache_size_label'):
                self.cache_size_label.config(text=f"最大缓存: {self.format_size(self.max_cache_size)} (10%)")
            if hasattr(self, 'cache_percent_label'):
                self.cache_percent_label.config(text="10%")
            
            # 应用默认字体大小
            self.apply_font_size(10)
            
            #　同步变量
            self.verify_chunks = self.verify_chunks_var.get()

            messagebox.showinfo("重置成功", "已恢复默认设置")
            self.log_message("设置已重置为默认值")

    def apply_theme(self, theme_name):
        """应用界面主题"""
        try:
            # 定义不同主题的配色方案
            themes = {
                "default": {
                    "bg": "#f0f0f0",
                    "fg": "#000000",
                    "button_bg": "#e1e1e1",
                    "button_fg": "#000000",
                    "accent": "#4a90e2"
                },
                "light": {
                    "bg": "#ffffff",
                    "fg": "#333333",
                    "button_bg": "#f5f5f5",
                    "button_fg": "#333333",
                    "accent": "#2196f3"
                },
                "dark": {
                    "bg": "#2b2b2b",
                    "fg": "#ffffff",
                    "button_bg": "#3d3d3d",
                    "button_fg": "#ffffff",
                    "accent": "#64b5f6"
                },
                "blue": {
                    "bg": "#e3f2fd",
                    "fg": "#1565c0",
                    "button_bg": "#bbdefb",
                    "button_fg": "#0d47a1",
                    "accent": "#1976d2"
                }
            }
            
            if theme_name not in themes:
                theme_name = "default"
            
            theme = themes[theme_name]
            
            # 应用主题到主窗口
            self.root.configure(bg=theme["bg"])
            
            # 更新所有Frame的背景色
            for widget in self.root.winfo_children():
                self._apply_theme_to_widget(widget, theme)
            
            self.log_message(f"已应用主题: {theme_name}")
            
        except Exception as e:
            self.log_message(f"应用主题失败: {e}")
    
    def start_http_listener(self, port=9876):
        """启动本地 HTTP 服务，用于接收浏览器扩展推送"""
        try:
            server = HTTPServer(('127.0.0.1', port), DownloaderRequestHandler)
            DownloaderRequestHandler.downloader_app = self
            t = threading.Thread(target=server.serve_forever, daemon=True)
            t.start()
            self.log_message(f"扩展监听已启动: http://127.0.0.1:{port}")
        except Exception as e:
            self.log_message(f"启动扩展监听失败: {e}")

    def apply_font_size(self, font_size):
        """应用字体大小到所有支持字体的组件"""
        try:
            # 定义基础字体族
            font_family = '微软雅黑'
            
            # 递归应用字体到所有widget
            self._apply_font_to_widget(self.root, font_family, font_size)
            
            self.log_message(f"已应用字体大小: {font_size}")
        except Exception as e:
            self.log_message(f"应用字体大小失败: {e}")
    
    def _apply_font_to_widget(self, widget, font_family, font_size):
        """递归应用字体到widget及其子widget"""
        try:
            # 检查widget是否支持font属性
            widget_type = widget.winfo_class()
            
            # 这些widget类型支持font属性
            if widget_type in ('Label', 'Button', 'Checkbutton', 'Radiobutton', 
                             'Menubutton', 'Message', 'Text', 'Entry'):
                try:
                    # 获取当前配置，保留其他属性
                    current_config = widget.config()
                    # 只更新font属性
                    widget.config(font=(font_family, font_size))
                except:
                    pass  # 忽略无法设置字体的widget
            
            # 递归处理Treeview的特殊情况
            elif widget_type == 'Treeview':
                try:
                    # Treeview需要使用ttk.Style来设置字体
                    style = ttk.Style()
                    style.configure('Treeview', font=(font_family, font_size - 1))
                    style.configure('Treeview.Heading', font=(font_family, font_size, 'bold'))
                except:
                    pass
            
            # 递归处理子widget
            for child in widget.winfo_children():
                self._apply_font_to_widget(child, font_family, font_size)
                
        except Exception as e:
            pass  # 忽略单个widget的字体应用错误
    
    def _apply_theme_to_widget(self, widget, theme):
        """递归应用主题到widget及其子widget"""
        try:
            # 根据widget类型应用不同的样式
            widget_type = widget.winfo_class()
            
            if widget_type in ('Frame', 'LabelFrame'):
                widget.configure(bg=theme["bg"])
            elif widget_type == 'Label':
                widget.configure(bg=theme["bg"], fg=theme["fg"])
            elif widget_type == 'Button':
                widget.configure(bg=theme["button_bg"], fg=theme["button_fg"])
            elif widget_type == 'Text':
                widget.configure(bg=theme["bg"], fg=theme["fg"], 
                               insertbackground=theme["fg"])
            
            # 递归处理子widget
            for child in widget.winfo_children():
                self._apply_theme_to_widget(child, theme)
                
        except Exception as e:
            pass  # 忽略单个widget的样式应用错误

    def on_tree_right_click(self, event):
        """处理Treeview右键点击事件"""
        # 获取点击位置
        item_id = self.task_tree.identify_row(event.y)
        
        if not item_id:
            return
            
        # 获取点击位置的行号
        row_index = self.task_tree.index(item_id)
        if 0 <= row_index < len(self.tasks):
            self.selected_task = self.tasks[row_index]
            
            # 显示右键菜单
            self.context_menu.post(event.x_root, event.y_root)
            
    def copy_download_url(self):
        """复制下载链接到剪贴板"""
        if self.selected_task:
            self.root.clipboard_clear()
            self.root.clipboard_append(self.selected_task.url)
            self.log_message(f"已复制下载链接: {self.selected_task.url}")
            
    def log_message(self, message):
        """线程安全的日志记录"""
        def _log():
            self.log_text.config(state=tk.NORMAL)
            self.log_text.insert(tk.END, f"[{datetime.now().strftime('%H:%M:%S')}] {message}\n")
            self.log_text.see(tk.END)
            self.log_text.config(state=tk.DISABLED)
        self.root.after(0, _log)
        
    def toggle_task_pause(self):
        """暂停/继续任务"""
        if self.selected_task:
            if self.selected_task.is_paused:
                self.selected_task.resume_download()
            else:
                self.selected_task.pause_download()
    
    def delete_selected_context_task(self):
        """删除选中的任务"""
        if self.selected_task:
            self.delete_task(self.selected_task)
            
    def clear_url(self):
        """清除URL输入"""
        self.url_var.set("")
        self.path_var.set("")

    def on_url_change(self, *args):
        """URL内容变化时的回调"""
        url = self.url_var.get().strip()
        if url:
            filename = self.extract_filename(url)
            current_path = self.path_var.get()
            if not current_path or os.path.isdir(current_path) or not os.path.basename(current_path):
                # 默认保存到下载目录
                download_dir = os.path.expanduser("~/Downloads")
                suggested = os.path.join(download_dir, filename)
                unique_path = self.get_unique_filename(suggested)
                self.path_var.set(unique_path)
        else:
            self.path_var.set("")

    def extract_filename(self, url):
        """从URL中提取文件名并解码URL编码"""
        try:
            parsed = urlparse(url)
            path = parsed.path
            filename = os.path.basename(path)
            if not filename or '.' not in filename:
                # 生成基于当前时间的文件名
                timestamp = datetime.now().strftime("%Y%m%d%H%M%S")
                return f"download_{timestamp}.bin"
            # 解码URL编码
            return unquote(filename)
        except Exception as e:
            self.log_message(f"提取文件名错误: {e}")
            return f"download_{int(threading.get_ident())}.bin"

    def get_unique_filename(self, filename):
        """获取不冲突的文件名"""
        if not os.path.exists(filename):
            return filename
            
        base, ext = os.path.splitext(filename)
        counter = 1
        new_filename = f"{base}({counter}){ext}"
        
        while os.path.exists(new_filename):
            counter += 1
            new_filename = f"{base}({counter}){ext}"
            
        return new_filename

    def browse_path(self):
        """浏览文件夹并自动填充文件名"""
        # 获取从URL提取的文件名
        url = self.url_var.get().strip()
        if url:
            filename = self.extract_filename(url)
        else:
            filename = "download.bin"
        
        # 默认目录设为下载目录
        initial_dir = os.path.expanduser("~/Downloads")
        if not os.path.exists(initial_dir):
            initial_dir = os.path.expanduser("~")
        
        # 生成唯一文件名
        base, ext = os.path.splitext(filename)
        counter = 1
        unique_filename = filename
        while os.path.exists(os.path.join(initial_dir, unique_filename)):
            unique_filename = f"{base}({counter}){ext}"
            counter += 1
        
        file_path = filedialog.asksaveasfilename(
            initialdir=initial_dir,
            initialfile=unique_filename,
            title="选择保存位置",
            defaultextension=".*",
            filetypes=[("所有文件", "*.*")]
        )
        
        if file_path:
            self.path_var.set(file_path)

    def start_download(self):
        """启动下载任务"""
        url = self.url_var.get().strip()
        save_path = self.path_var.get().strip()
        thread_count = min(max(1, self.thread_var.get()), self.max_threads)
        
        if not url:
            messagebox.showwarning("提示", "请输入有效的下载链接")
            return
            
        # 自动添加协议
        if not url.startswith(('http://', 'https://', 'ftp://', 'file://', 'blob:')):
            if '.' in url and '/' in url:
                url = 'https://' + url
                self.url_var.set(url)
            else:
                messagebox.showwarning("提示", "无效的URL格式")
                return

        if not save_path:
            messagebox.showwarning("提示", "请选择保存路径")
            return

        # 检查目标目录是否可写
        save_dir = os.path.dirname(save_path)
        if not os.access(save_dir, os.W_OK):
            response = messagebox.askyesno("权限错误", 
                                          f"没有权限写入目录: {save_dir}\n"
                                          "是否要选择其他目录?")
            if response:
                self.browse_path()
                save_path = self.path_var.get().strip()
                save_dir = os.path.dirname(save_path)
                if not os.access(save_dir, os.W_OK):
                    messagebox.showerror("权限错误", "仍然无法写入该目录，请选择其他目录")
                    return
            else:
                return
            
        # 确保使用唯一文件名
        if os.path.exists(save_path):
            save_path = self.get_unique_filename(save_path)
            self.path_var.set(save_path)
        
        # 创建新任务
        task = DownloadTask(url, save_path, self)
        task.thread_count = min(self.thread_var.get(), self.max_threads)
        
        with self.lock:
            self.tasks.append(task)
        
        # 在UI中添加新任务
        self.add_task_to_tree(task)
        
        # 启动下载线程
        threading.Thread(target=task.start_multithread_download, daemon=True).start()
        
        self.log_message(f"开始下载: {url} → {save_path}")
        self.log_message(f"使用 {thread_count} 线程和分块下载")
        
        # 切换到任务页
        self.notebook.select(1)
        
        # 清空输入框
        self.url_var.set("")
        self.path_var.set("")

    def add_task_to_tree(self, task):
        """添加单个任务到Treeview - 错误任务使用红色文本"""
        # 格式化大小信息
        if task.total_size > 0:
            size_info = f"{self.format_size(task.downloaded_size)} / {self.format_size(task.total_size)}"
        else:
            size_info = "未知大小"
            
        # 操作按钮文本
        if task.is_completed:
            action_text = "打开文件 | 删除"
        elif task.status.startswith("错误") or task.status.startswith("权限错误") or task.status.startswith("路径错误") or task.status.startswith("网络错误"):
            action_text = "重试 | 删除"
        else:
            action_text = "暂停" if not task.is_paused else "继续"
            
        # 添加到Treeview
        if task.status.startswith("错误") or task.status.startswith("权限错误") or task.status.startswith("路径错误") or task.status.startswith("网络错误"):
            item_id = self.task_tree.insert("", tk.END, values=(
                task.url, 
                task.status, 
                f"{task.downloaded_size / task.total_size * 100:.1f}%" if task.total_size > 0 else "0%",
                size_info,
                task.time_info,
                self.format_size(0),  # 缓存使用
                action_text
            ), tags=("error",))
            self.task_tree.tag_configure("error", foreground="red")
        else:
            item_id = self.task_tree.insert("", tk.END, values=(
                task.url, 
                task.status, 
                f"{task.downloaded_size / task.total_size * 100:.1f}%" if task.total_size > 0 else "0%",
                size_info,
                task.time_info,
                self.format_size(0),  # 缓存使用
                action_text
            ))
            
        task.tree_item = item_id

    def retry_task(self, task):
        """重试失败的任务"""
        # 清除错误状态
        task.status = "准备重新下载"
        task.is_downloading = False
        task.is_paused = False
        task.is_completed = False
        
        # 重置进度
        task.downloaded_size = 0
        task.download_start_time = None
        task.last_update_time = None
        
        # 清除临时文件
        temp_dir = os.path.join(os.path.dirname(task.save_path), f".{task.task_id}")
        if os.path.exists(temp_dir):
            try:
                shutil.rmtree(temp_dir)
            except Exception as e:
                self.log_message(f"删除临时目录失败: {e}")
        
        # 重置分块信息
        task.chunks = []
        
        # 更新UI
        self.update_task_row(task)
        
        # 重新开始下载
        task.resume_download()
        
    def on_tree_click(self, event):
        """处理Treeview点击事件"""
        # 获取点击位置
        item_id = self.task_tree.identify_row(event.y)
        column = self.task_tree.identify_column(event.x)
        
        if not item_id:
            return
            
        # 获取点击位置的行号
        row_index = self.task_tree.index(item_id)
        if 0 <= row_index < len(self.tasks):
            task = self.tasks[row_index]
            
            if column == "#7":  # 第7列是操作列
                # 获取操作列的边界
                bbox = self.task_tree.bbox(item_id, column="action")
                if not bbox:
                    return
                
                # 计算在操作列内的相对位置
                action_col_x = event.x - bbox[0]
                width = bbox[2]
                
                # 如果点击在左半部分
                if action_col_x < width / 2:
                    if task.is_completed:
                        self.open_file(task)
                    elif task.status.startswith("错误") or task.status.startswith("权限错误") or task.status.startswith("路径错误") or task.status.startswith("网络错误"):
                        self.retry_task(task)
                    else:
                        if task.is_paused:
                            task.resume_download()
                        else:
                            task.pause_download()
                else:  # 点击在右半部分，删除任务
                    self.delete_task(task)
                
                # 更新UI
                self.update_task_row(task)
    
    def open_file(self, task):
        """打开下载的文件"""
        if os.path.exists(task.save_path):
            try:
                # 根据操作系统打开文件
                if os.name == 'nt':  # Windows
                    os.startfile(task.save_path)
                elif os.name == 'posix':  # macOS or Linux
                    subprocess.call(('open', task.save_path))
                else:
                    messagebox.showinfo("打开文件", f"文件位置: {task.save_path}")
            except Exception as e:
                messagebox.showerror("错误", f"无法打开文件: {e}")
        else:
            messagebox.showwarning("警告", "文件不存在")
    
    def delete_task(self, task):
        """删除单个任务，如果未完成则删除已下载的文件"""
        if messagebox.askyesno("确认删除", f"确定要删除任务: {os.path.basename(task.save_path)} 吗?"):
            # 暂停任务
            task.pause_download()
            
            # 如果任务未完成，删除相关文件
            if not task.is_completed:
                # 1. 删除临时分块目录
                temp_dir = os.path.join(os.path.dirname(task.save_path), f".{task.task_id}")
                if os.path.exists(temp_dir):
                    try:
                        shutil.rmtree(temp_dir)
                        self.log_message(f"已删除临时目录: {temp_dir}")
                    except Exception as e:
                        self.log_message(f"删除临时目录失败: {e}")
                
                # 2. 删除目标文件（如果存在且不完整）
                if os.path.exists(task.save_path):
                    try:
                        os.remove(task.save_path)
                        self.log_message(f"已删除未完成文件: {task.save_path}")
                    except Exception as e:
                        self.log_message(f"删除未完成文件失败: {e}")
            else:
                # 已完成的任务，只清理可能残留的临时目录（一般已被删除）
                temp_dir = os.path.join(os.path.dirname(task.save_path), f".{task.task_id}")
                if os.path.exists(temp_dir):
                    try:
                        shutil.rmtree(temp_dir)
                    except:
                        pass
            
            # 从任务列表中移除
            with self.lock:
                if task in self.tasks:
                    self.tasks.remove(task)
            
            # 从Treeview中移除
            if task.tree_item and self.task_tree.exists(task.tree_item):
                self.task_tree.delete(task.tree_item)
            
            # 清除断点续传信息
            self.clear_resume_info(task.task_id)
    
    def delete_selected_task(self):
        """删除选中的任务"""
        selected_items = self.task_tree.selection()
        if not selected_items:
            messagebox.showwarning("提示", "请先选择一个任务")
            return
            
        for item in selected_items:
            # 查找对应的任务
            for task in self.tasks:
                if task.tree_item == item:
                    self.delete_task(task)
                    break
    
    def delete_all_tasks(self):
        """删除所有任务，并清理未完成任务的下载文件"""
        if not self.tasks:
            return
            
        if messagebox.askyesno("确认删除", "确定要删除所有任务吗？未完成的任务文件也会被删除。"):
            # 遍历所有任务，先暂停并清理文件
            for task in self.tasks:
                task.pause_download()
                if not task.is_completed:
                    # 删除临时目录
                    temp_dir = os.path.join(os.path.dirname(task.save_path), f".{task.task_id}")
                    if os.path.exists(temp_dir):
                        try:
                            shutil.rmtree(temp_dir)
                        except:
                            pass
                    # 删除目标文件
                    if os.path.exists(task.save_path):
                        try:
                            os.remove(task.save_path)
                        except:
                            pass
            
            # 清空任务列表
            with self.lock:
                self.tasks.clear()
            
            # 清空Treeview
            for item in self.task_tree.get_children():
                self.task_tree.delete(item)
            
            # 清除断点续传信息
            if os.path.exists("resume_info.json"):
                try:
                    with open("resume_info.json", "w") as f:
                        json.dump({}, f)
                except Exception as e:
                    self.log_message(f"清除断点续传信息失败: {e}")
            
            self.log_message("已删除所有任务及未完成的文件")
    
    def stop_all_tasks(self):
        """暂停所有任务"""
        for task in self.tasks:
            if not task.is_completed and not task.is_paused:
                task.pause_download()
        
        messagebox.showinfo("操作完成", "所有任务已暂停")
        self.log_message("所有任务已暂停")
    
    def start_all_tasks(self):
        """开始所有暂停的任务"""
        started = 0
        for task in self.tasks:
            if not task.is_completed and task.is_paused:
                task.resume_download()
                started += 1
        
        if started > 0:
            messagebox.showinfo("操作完成", f"已启动 {started} 个任务")
            self.log_message(f"已启动 {started} 个任务")
        else:
            messagebox.showinfo("操作完成", "没有需要启动的任务")

    def clear_resume_info(self, download_id):
        """清除断点续传信息"""
        if os.path.exists("resume_info.json"):
            try:
                with open("resume_info.json", "r+") as f:
                    data = json.load(f)
                    if download_id in data:
                        del data[download_id]
                        f.seek(0)
                        json.dump(data, f, indent=4)
                        f.truncate()
            except Exception as e:
                self.log_message(f"清除断点续传信息失败: {e}")
                
    def load_resume_info(self):
        """加载断点续传信息"""
        if os.path.exists("resume_info.json"):
            try:
                with open("resume_info.json", "r") as f:
                    data = json.load(f)
                    
                # 恢复下载任务
                for url_hash, task_info in data.items():
                    task = DownloadTask(task_info["url"], task_info["path"], self)
                    task.downloaded_size = task_info["downloaded_size"]
                    task.total_size = task_info["total_size"]
                    task.status = task_info["status"]
                    task.is_paused = task_info.get("is_paused", False)
                    
                    # 添加到任务列表
                    self.tasks.append(task)
                    
                    # 添加到Treeview显示
                    self.add_task_to_tree(task)
                    
                self.log_message(f"加载了 {len(data)} 个断点续传任务")
            except Exception as e:
                self.log_message(f"加载断点续传信息失败: {e}")
                
    def save_resume_info(self):
        """保存下载信息用于断点续传"""
        try:
            info = {}
            for task in self.tasks:
                if not task.is_completed:
                    task_info = {
                        "url": task.url,
                        "path": task.save_path,
                        "downloaded_size": task.downloaded_size,
                        "total_size": task.total_size,
                        "status": task.status,
                        "is_paused": task.is_paused
                    }
                    info[task.task_id] = task_info
            
            # 保存到JSON
            with open("resume_info.json", "w") as f:
                json.dump(info, f, indent=4)
        except PermissionError:
            self.log_message("保存断点续传信息失败: 权限不足，无法写入resume_info.json文件")
        except Exception as e:
            self.log_message(f"保存断点续传信息失败: {e}")
            
    def update_memory_info(self):
        """更新内存信息显示"""
        try:
            mem = psutil.virtual_memory()
            used_percent = mem.percent
            cached_percent = (self.total_cached / self.total_memory) * 100
            
            text = f"内存使用: {used_percent:.1f}% (缓存: {cached_percent:.1f}%) | "
            text += f"总内存: {self.format_size(self.total_memory)} | "
            text += f"已用: {self.format_size(mem.used)} | "
            text += f"空闲: {self.format_size(mem.available)}"
            
            self.mem_info.config(text=text)
            
            # 10秒后再次更新
            self.root.after(10000, self.update_memory_info)
        except:
            pass
    
    def update_network_info(self):
        """更新网络吞吐量信息"""
        try:
            # 获取当前网络IO数据
            current_net_io = psutil.net_io_counters()
            current_time = time.time()
            
            # 计算时间差
            time_diff = current_time - self.last_net_time
            
            # 避免除零错误
            if time_diff > 0:
                # 计算下载速度 (字节/秒)
                download_speed = (current_net_io.bytes_recv - self.last_net_io.bytes_recv) / time_diff
                # 计算上传速度 (字节/秒)
                upload_speed = (current_net_io.bytes_sent - self.last_net_io.bytes_sent) / time_diff
                
                # 保存当前值用于下一次计算
                self.last_net_io = current_net_io
                self.last_net_time = current_time
                
                # 更新UI
                self.download_speed_label.config(text=f"下载速度: {self.format_size(download_speed)}/s")
                self.upload_speed_label.config(text=f"上传速度: {self.format_size(upload_speed)}/s")
                
                # 保存速度信息
                self.net_speed_info = {
                    "download": download_speed,
                    "upload": upload_speed
                }
        
        except Exception as e:
            self.log_message(f"网络监控错误: {e}")
        
        # 1秒后再次更新
        self.root.after(1000, self.update_network_info)
            
    def format_size(self, size_bytes):
        """格式化文件大小显示"""
        if size_bytes < 1024:
            return f"{size_bytes} B"
        elif size_bytes < 1024 * 1024:
            return f"{size_bytes/1024:.1f} KB"
        elif size_bytes < 1024 * 1024 * 1024:
            return f"{size_bytes/(1024 * 1024):.1f} MB"
        else:
            return f"{size_bytes/(1024 * 1024 * 1024):.1f} GB"
            
    def format_time(self, seconds):
        """格式化时间"""
        if seconds < 60:
            return f"{int(seconds)}秒"
        elif seconds < 3600:
            minutes = int(seconds / 60)
            seconds = int(seconds % 60)
            return f"{minutes}分{seconds}秒"
        else:
            hours = int(seconds / 3600)
            minutes = int((seconds % 3600) / 60)
            return f"{hours}时{minutes}分"

    def refresh_task_list(self):
        """刷新任务列表显示 - 立即刷新"""
        # 清空现有项目并重新创建
        for item in self.task_tree.get_children():
            self.task_tree.delete(item)
        
        # 添加所有任务
        for task in self.tasks:
            self.add_task_to_tree(task)
        
    def update_task_row(self, task):
        """更新单个任务在Treeview中的显示 - 增强错误处理"""
        if not task.tree_item or not self.task_tree.exists(task.tree_item):
            return
            
        ''' 准备要显示的值 '''
        # 格式化大小信息
        if task.size_info:
            size_info = task.size_info
        else:
            if task.total_size > 0:
                size_info = f"{self.format_size(task.downloaded_size)} / {self.format_size(task.total_size)}"
            else:
                size_info = "未知大小"

        # 格式化时间信息
        if task.time_info:
            time_info = task.time_info
        else:
            time_info = "未知"

        # 进度百分比
        if task.total_size > 0:
            progress = f"{task.downloaded_size / task.total_size * 100:.1f}%"
        else:
            progress = "0%"

        # 操作按钮文本
        cooldown_remaining = 0
        if task.is_completed:
            action_text = "打开文件 | 删除"
        elif task.status.startswith("错误") or task.status.startswith("权限错误") or task.status.startswith("路径错误") or task.status.startswith("网络错误"):
            action_text = "重试 | 删除"
        else:
            # 计算冷却时间剩余
            cooldown_remaining = max(0, task.operation_cooldown - (time.time() - task.last_operation_time))
            
            if cooldown_remaining > 0:
                # 显示冷却中提示
                action_text = f"冷却中({cooldown_remaining:.1f}s)"
            else:
                if task.is_paused:
                    action_text = "继续"
                else:
                    action_text = "暂停"
                    
        # 缓存使用信息
        cache_info = self.format_size(0)  # 不再使用内存缓存

        # 更新Treeview
        self.task_tree.item(task.tree_item, values=(
            task.url, 
            task.status, 
            progress,
            size_info,
            time_info,
            cache_info,
            action_text
        ))
        
        # 如果仍在冷却中，安排再次更新
        if cooldown_remaining > 0:
            self.root.after(200, lambda: self.update_task_row(task))

    def on_close(self):
        """处理窗口关闭事件"""
        # 暂停所有任务
        for task in self.tasks:
            if not task.is_paused:
                task.pause_download()
    
        # 保存断点续传信息
        self.save_resume_info()
        self.root.destroy()

if __name__ == "__main__":
    root = tk.Tk()
    app = SmartDownloader(root)
    root.mainloop()