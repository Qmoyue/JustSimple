# 构建与使用

## 构建

先装 JDK 17 或更新版本和 Maven。用 `java -version` 和 `mvn -v` 确认终端能找到它们，再克隆源码。

```sh
git clone https://github.com/Qmoyue/JustSimple.git
cd JustSimple
```

后面的命令都在仓库根目录执行。扫描时要选目标程序所用的 Java 类库。比如目标程序跑在 Java 8 上，就把示例里的 `path/to/target-jdk` 换成 Java 8 的安装目录。Scanner 会从这个目录读取 `rt.jar` 或 `jmods/`。

## Scanner

只想从命令行扫描，运行下面两条命令。把应用和 JDK 路径换成你的路径，输出目录用一个还不存在的目录。

```sh
mvn -pl scanner -DskipTests package
java -jar scanner/target/justsimple-0.1.0.jar --input "path/to/app.jar" --jdk-home "path/to/target-jdk" --output ".local/results/scan"
```

扫完先打开输出目录里的 `report.md`。`--input` 也接受 WAR、单个 `.class` 文件或类目录。需要补依赖时，可以多次使用 `--dependency` 指定 JAR 或类目录。默认按应用扫描，扫描独立组件时加 `--mode component`。

用 `java -jar scanner/target/justsimple-0.1.0.jar --help` 查看全部参数。已有对象或参数信息时，可以用 `--facts` 提供静态数据。退出码 `0` 表示扫描完成，`3` 表示扫描受限，`2` 表示失败。进度写到 stderr，最终状态写到 stdout。[报告格式](reference/evidence.md#扫描报告) · [静态数据格式](reference/static-data.md)

## Agent

要使用交互终端，再准备 Node.js 22.19.0 或更新版本和 pnpm 11。下面的命令会一起构建 Scanner 和 Bridge，再启动 Agent。

```sh
mvn -DskipTests package
pnpm install --frozen-lockfile
pnpm build
pnpm agent
```

打开 Agent 后，先选要扫描的文件，再选它用的 Java 安装目录。这个目录还要有 `release` 文件。

```text
/target "path/to/app.jar"
/jdk-home "path/to/target-jdk"
/scan-only
```

`/scan-only` 不需要登录模型。第一次用它时，可以按 Enter 接受默认的扫描选项。报告默认保存到工作目录下的 `.local/scans/scan-<ID>/`。

如果想让模型帮你继续查，用 `/login` 登录、`/model` 选模型，再输入 `/agent`，就可以在对话里提问。会话上下文和工具结果会发给所选的模型服务。[交互审计](reference/audit.md)

交互审计按需读取内置 Skill。目标目录或工作目录里的 `.agent/skills/` 和 `.agents/skills/` 都不会自动加载。本次审计有额外规则，可以直接发到对话里。

相对路径以工作目录为准，用 `/workspace` 可以切换。依赖可用 `--dependency` 加入，填路径或 `group:artifact:version` 都可以。Maven 坐标从本地仓库查找，默认是 `~/.m2/repository`，用 `/maven-home` 可以更换。

用 `/board` 查看当前问题和证据，按 Esc 中断任务，或用 `/home` 回到首页。其他命令和参数见 `/help`。

## 本地记录

Agent 把扫描偏好、模型配置、会话和审计任务保存在启动目录的 `.local/agent/`。用 `pnpm agent --agent-dir "path/to/state"` 可以换个保存位置。启动时也可以用 `--cwd` 设工作目录，用 `--jdk-home` 选目标的 Java 安装目录。

## 开发验证

`mvn test` 运行 Java 测试。构建两个 JAR 和 Agent 后，设置 `JAVA_HOME`，再用 `pnpm test` 运行 Agent 和仓库检查的测试。`pnpm check` 检查仓库和 TypeScript，单独检查仓库和文档可以用 `pnpm check:repo`。[开发约束](../AGENTS.md)
