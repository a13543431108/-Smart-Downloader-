document.getElementById('save').addEventListener('click', () => {
  const server = document.getElementById('server').value.trim();
  chrome.storage.local.set({ server }, () => {
    alert('设置已保存');
  });
});