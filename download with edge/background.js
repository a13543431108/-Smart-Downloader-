// ========== 配置 ==========
const DEFAULT_SERVER = 'http://127.0.0.1:9876';
let targetServer = DEFAULT_SERVER;
let downloaderAvailable = false;

// ========== 请求头缓存（用于接管敏感链接） ==========
const requestHeadersCache = new Map();
const CACHE_TTL = 60000; // 缓存 60 秒

// ========== 加载用户自定义服务器地址 ==========
chrome.storage.local.get(['server'], (result) => {
  if (result.server) targetServer = result.server;
  checkDownloaderStatus();
});

// ========== 定期检测下载器状态 ==========
function checkDownloaderStatus() {
  fetch(`${targetServer}/status`)
    .then(response => {
      downloaderAvailable = response.ok;
      console.log('[SmartDownload] 下载器状态:', downloaderAvailable ? '在线' : '离线');
    })
    .catch(() => {
      downloaderAvailable = false;
      console.log('[SmartDownload] 下载器离线');
    });
}
setInterval(checkDownloaderStatus, 15000);

// ========== 抓取请求头（Cookie、Authorization 等） ==========
chrome.webRequest.onBeforeSendHeaders.addListener(
  (details) => {
    // 只缓存 GET 请求的敏感头
    if (details.method !== 'GET' || details.tabId === -1) return;

    const important = {};
    details.requestHeaders.forEach(header => {
      const name = header.name.toLowerCase();
      if (['cookie', 'authorization', 'x-csrf-token'].includes(name)) {
        important[name] = header.value;
      }
    });

    if (Object.keys(important).length > 0) {
      requestHeadersCache.set(details.url, {
        headers: important,
        timestamp: Date.now()
      });
    }
  },
  { urls: ['<all_urls>'] },
  ['requestHeaders']
);

// 定期清理过期缓存（每 30 秒）
setInterval(() => {
  const now = Date.now();
  for (const [url, entry] of requestHeadersCache) {
    if (now - entry.timestamp > CACHE_TTL) {
      requestHeadersCache.delete(url);
    }
  }
}, 30000);

// ========== 判断是否应由浏览器自己下载 ==========
function shouldKeepBrowserDownload(url) {
  // 浏览器内部协议（blob:, data:, filesystem: 等）
  return /^(blob|data|filesystem|javascript|about):/i.test(url);
}

// ========== 拦截浏览器下载 ==========
chrome.downloads.onCreated.addListener((downloadItem) => {
  const url = downloadItem.url;

  // 浏览器内部协议 → 放行
  if (shouldKeepBrowserDownload(url)) {
    console.log('[SmartDownload] 内部协议，保留浏览器下载:', url);
    return;
  }

  // 下载器未运行 → 放行
  if (!downloaderAvailable) {
    return;
  }

  // 尝试接管：取消浏览器下载并转发（带 Cookie 头）
  chrome.downloads.cancel(downloadItem.id, () => {
    if (chrome.runtime.lastError) {
      console.warn('[SmartDownload] 取消失败:', chrome.runtime.lastError.message);
    } else {
      sendToDownloader(downloadItem.url, downloadItem.filename);
    }
  });
});

// ========== 发送下载链接 + 认证头到本地下载器 ==========
function sendToDownloader(url, suggestedFilename) {
  // 尝试从缓存中获取请求头
  let headers = null;
  const cached = requestHeadersCache.get(url);
  if (cached) {
    headers = cached.headers;
    requestHeadersCache.delete(url);  // 使用后即删
  }

  const payload = {
    url: url,
    filename: suggestedFilename || '',
    headers: headers    // 可以是 null 或对象
  };

  fetch(`${targetServer}/add_task`, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(payload)
  })
  .then(response => {
    if (response.ok) console.log('[SmartDownload] 已发送（含认证信息）:', url);
  })
  .catch(err => {
    console.warn('[SmartDownload] 发送失败:', err.message);
    downloaderAvailable = false;   // 标记离线，下次点击恢复浏览器下载
  });
}