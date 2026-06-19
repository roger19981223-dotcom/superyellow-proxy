# SuperYellow Proxy

[English](README_EN.md) | **中文**

## 简介

SuperYellow Proxy 是一个基于 WebSocket 的隧道代理，通过 6 条 TCP 流并行传输 + 自适应 FEC 纠错 + uTLS 指纹伪装，实现弱网环境下的稳定翻墙访问。客户端提供 SOCKS5 / HTTP CONNECT 代理入口，兼容 PassWall、Xray、SagerNet 等主流工具。

## 特性

- **6 条 TCP 流并行** — 多流复用提升吞吐，单一流故障自动隔离
- **自适应 FEC 纠错** — 动态调整冗余比率（6 流→5+1，5 流→4+2，<3 流→1+2），弱网下保持可用
- **分离控制/数据通道** — 控制帧走 1+2 FEC 快车道（`FastLaneFlag`），数据帧走 5+1 FEC，互不污染
- **类型 6 FIN 帧** — 优雅 EOF，确保数据顺序写入后再关闭连接，不再丢包
- **uTLS 指纹伪装** — TLS 握手与浏览器完全一致，SNI demux 回落到正常网页
- **SOCKS5 / HTTP CONNECT** — 标准代理协议，支持 UDP ASSOCIATE
- **单流自愈 + 退避重连** — 故障流自动替换，全断时指数退避重连（2s→30s）
- **低日志噪音** — 默认关闭连接级 debug 日志，CMD3 Mux 限频告警
- **N100 性能优化** — GC=200%、64MB 重组缓冲、5×MSS 读取窗口

## 下载

| 平台 | 文件 | 说明 |
|------|------|------|
| Windows | `superyellow-windows-amd64.exe` | 命令行客户端 |
| Android | `SuperYellow-Proxy-v1.0.apk` | Android 客户端 |
| iStoreOS/OpenWrt | `SuperYellow_Client_v1.2.2_x86_64.run` | 路由器插件 (x86_64) |

👉 [GitHub Releases](https://github.com/roger19981223-dotcom/superyellow-proxy/releases)

## 服务端部署

### 环境要求

- Linux 服务器 (推荐 Ubuntu/Debian)
- 公网 IP
- 域名（可选，用于 TLS）

### 安装

```bash
# 下载服务端
wget https://github.com/roger19981223-dotcom/superyellow-proxy/releases/latest/download/aether-server-linux-arm64

# 创建配置目录
mkdir -p ~/aether-server

# 创建配置文件
cat > ~/aether-server/aether_config.json << 'EOF'
{
  "panel_port": "8080",
  "listen_port": "8443",
  "camo_mode": "self",
  "panel_user": "admin",
  "panel_pass": "your-password-here"
}
EOF

# 启动
chmod +x aether-server-linux-arm64
./aether-server-linux-arm64
```

### systemd 服务

```bash
cat > /etc/systemd/system/aether-server.service << 'EOF'
[Unit]
Description=SuperYellow Proxy Server
After=network.target

[Service]
Type=simple
User=root
WorkingDirectory=/home/ubuntu/aether-server
ExecStart=/home/ubuntu/aether-server/aether-server
Restart=always
RestartSec=5

[Install]
WantedBy=multi-user.target
EOF

systemctl daemon-reload
systemctl enable aether-server
systemctl start aether-server
```

## 客户端使用

### Windows

```cmd
superyellow-windows-amd64.exe
```

浏览器打开 `http://127.0.0.1:9999` 配置服务器信息。

### iStoreOS/OpenWrt 路由器

1. 上传 `.run` 文件到路由器 `/tmp/`
2. SSH 登录路由器执行：
   ```bash
   sh /tmp/SuperYellow_Client_v1.2.2_x86_64.run
   ```
3. 打开 Web 面板 `http://<路由器IP>:9999`，填入服务器信息
4. 在 PassWall 中添加节点：
   - 类型：Xray
   - 协议：SOCKS5
   - 地址：`127.0.0.1`
   - 端口：`11080`
   - 关闭 Mux（Aether 自带多路复用，嵌套 Mux 会断网）
5. 在 PassWall 中切换到 SuperYellow 节点

### Android

安装 `SuperYellow-Proxy-v1.0.apk`，在应用内配置服务器信息。

## 配置说明

### 服务端配置 (aether_config.json)

| 字段 | 说明 | 示例 |
|------|------|------|
| `panel_port` | 管理面板端口 | `8080` |
| `listen_port` | 隧道监听端口 | `8443` |
| `camo_mode` | 伪装模式 | `self`（返回 nginx 默认页） |
| `panel_user` | 面板用户名 | `admin` |
| `panel_pass` | 面板密码 | `your-password` |
| `domain` | 域名（启用 ACME 自动证书） | `example.com` |

### 客户端配置 (superyellow_client.json)

| 字段 | 说明 | 示例 |
|------|------|------|
| `server` | 服务器地址:端口 | `1.2.3.4:8443` |
| `username` | 用户名 | `Default` |
| `password` | 密码 | `your-password` |
| `sni` | SNI 域名（需与服务端 domain 一致） | `example.com` |

## 技术参数

| 参数 | 值 |
|------|-----|
| TCP 流数量 | 6 |
| FEC 动态策略 | 6→5+1, 5→4+2, <3→1+2 |
| 数据通道 FEC | 5+1 (5 数据 + 1 校验) |
| 控制通道 FEC | 1+2 (任意 1/3 可恢复) |
| TLS 版本 | 1.3 |
| ALPN | http/1.1 |
| 客户端代理端口 | 11080 (SOCKS5/HTTP) |
| 客户端面板端口 | 9999 |
| 服务端面板端口 | 8080 |
| 服务端隧道端口 | 8443 |
| 重组缓冲 | 64 MB |
| TCP Buffer | 2 MB |
| 写超时 | 5s |
| 帧协议版本 | ProtocolVersion=3 |

## License

MIT
