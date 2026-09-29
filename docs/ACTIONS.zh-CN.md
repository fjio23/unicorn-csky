# GitHub Actions 入门：这个仓库怎么用

Actions 可以理解为 GitHub 提供的一台临时电脑。你提交代码后，它会自动拉取
代码、安装工具、编译并运行测试。配置文件在
[.github/workflows/csky-ci.yml](../.github/workflows/csky-ci.yml)。

## 已配置的流程

`C-SKY CI` 在以下情况运行：

- 向 `main` 分支推送代码。
- 创建或更新目标分支为 `main` 的 Pull Request。
- 在网页上手动点击 **Run workflow**。

每次运行有两个 job（任务），两者同时执行：

| 任务 | 内容 |
| --- | --- |
| Linux / csky-only | 只构建 C-SKY，运行 C-SKY C 测试、Python 测试和 C 示例；成功后打包库、头文件和 Python 绑定 |
| Linux / all-architectures | 构建所有架构，运行完整 CTest 回归测试，再运行 C-SKY Python 测试和 C 示例 |

两个任务使用 Ubuntu 24.04 x86-64 和 Python 3.12。无需安装 C-SKY 交叉编译器，
也无需添加 Secrets（密钥）。同一分支又有新提交时，旧的一轮会取消，改测最新代码。

上游留下的 Build UC2、Zig、wheel、Crate、NuGet 及 Release 流程保留为手动运行。
日常只使用 **C-SKY CI**。这些旧发布流程尚未针对本仓库配置，可能依赖额外密钥和
上游分支名；不要把它们当作已经可用的发布入口。

## 第一次查看

1. 打开 [Actions 页面](https://github.com/fjio23/unicorn-csky/actions)。
2. 左侧选择 **C-SKY CI**，点击最新一次运行。
3. 黄色表示正在等待或执行，绿色表示通过，红色表示失败，灰色通常表示取消或跳过。
4. 点击一个任务，再展开具体步骤，就能看到完整命令和错误日志。

如果 GitHub 显示需要启用 Actions，按页面提示启用；也可以在
**Settings → Actions → General** 检查是否允许 GitHub Actions。

## 手动运行和重试

打开 **Actions → C-SKY CI → Run workflow**，选择 `main`，再点击绿色按钮。
按钮通常出现在流程列表右上方，需要登录有权限的账号。

某次运行失败后，先展开红色步骤查看原因。如果只是下载依赖等临时网络问题，
可以在该次运行右上方点 **Re-run jobs → Re-run failed jobs**。
如果是编译或测试失败，需要修代码，再提交；新的提交会自动重新检测。

## 下载编译产物

进入成功运行的详情页，下方 **Artifacts** 区域有：

- `unicorn-csky-linux-x86_64`：Linux 库、C 头文件、Python 绑定和示例源码，保留 14 天。
- `test-logs-csky-only` 和 `test-logs-all-architectures`：C 测试日志，保留 7 天。

下载可能需要登录 GitHub。下载的 ZIP 中包含 `unicorn-csky-linux-x86_64.tar.gz`，
继续解压这个 tar.gz。在解压后的目录中运行：

```sh
export PYTHONPATH="$PWD/bindings/python"
export LIBUNICORN_PATH="$PWD/lib"
python3 -c 'from unicorn import UC_ARCH_CSKY, uc_arch_supported; print(uc_arch_supported(UC_ARCH_CSKY))'
```

输出 `True` 表示加载成功，接下来可以运行 [CSKY.md](CSKY.md) 的示例。
产物是 Ubuntu 24.04 构建的 Linux x86-64 版本，需要兼容的 Linux 环境；不能直接
用于 Windows、macOS、ARM 主机或较旧的 glibc 系统。

Artifact 是某次构建的临时下载文件，**不是 GitHub Release，也不会发布到 PyPI**。

## 配置里常见的词

- `on`：什么时候触发。
- `jobs`：要执行哪些任务。
- `runs-on`：使用哪种临时电脑。
- `steps`：任务中按顺序执行的步骤。
- `run`：执行终端命令。
- `uses`：调用别人写好的 Action，例如 checkout 拉取代码、upload-artifact 上传文件。
- `matrix`：用同一套步骤跑不同配置；这里是“只构建 C-SKY”和“构建全部架构”。

现在日常只需要：修改代码 → `git push` → 去 Actions 看结果。
