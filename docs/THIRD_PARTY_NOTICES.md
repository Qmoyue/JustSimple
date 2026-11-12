# 第三方依赖许可

## Scanner

| 组件 | 版本 | 许可与来源 |
| --- | --- | --- |
| ASM、ASM Tree、ASM Analysis | 9.8 | [BSD-3-Clause](https://asm.ow2.io/license.html) · [随附文本](licenses/ASM-BSD-3-Clause.txt) |
| Gson | 2.13.2 | [Apache-2.0](https://github.com/google/gson/blob/gson-parent-2.13.2/LICENSE) · [随附文本](licenses/Apache-2.0.txt) |
| Error Prone Annotations | 2.41.0 | [Apache-2.0](https://github.com/google/error-prone/blob/v2.41.0/COPYING) · [随附文本](licenses/Apache-2.0.txt) |

- ASM: Copyright (c) 2000-2011 INRIA, France Telecom. All rights reserved.
- Gson: Copyright (C) 2008 Google Inc. Additional contributions retain their upstream notices.
- Error Prone Annotations: Copyright The Error Prone Authors.

本说明和 Java 依赖的许可文本位于 Scanner JAR 的 `META-INF/JustSimple/`。内置知识为本项目整理的通用结构关系与适用条件。

## Agent

| 依赖 | 用途 | 许可 |
| --- | --- | --- |
| [Pi SDK](https://github.com/earendil-works/pi) 1.4.0 | 模型会话、终端交互与工具契约 | MIT |
| [Pi TUI](https://github.com/earendil-works/pi/tree/main/packages/tui) 1.4.0 | 终端与按键处理 | MIT |
| [TypeBox](https://github.com/sinclairzx81/typebox) 1.3.27 | 参数 schema 与校验 | MIT |
| [TypeScript](https://github.com/microsoft/TypeScript) | 构建及类型检查 | Apache-2.0 |
| [Node 类型](https://github.com/DefinitelyTyped/DefinitelyTyped) | 开发类型 | MIT |

版本与传递依赖见[锁文件](../pnpm-lock.yaml)，许可证随各依赖分发。[Pi SDK 补丁](../agent/patches/pi-coding-agent-1.4.0.patch)增加可选的终端界面开关，[Pi TUI 补丁](../agent/patches/pi-tui-1.4.0.patch)支持关闭自动复制后用 Ctrl+C 或右键复制。

## Java 测试

以下依赖仅用于测试。

| 组件 | 版本 | 许可 |
| --- | --- | --- |
| JUnit Jupiter / JUnit Platform | 5.10.2 / 1.10.2 | [EPL-2.0](https://github.com/junit-team/junit5/blob/r5.10.2/LICENSE.md) |
| OpenTest4J | 1.3.0 | [Apache-2.0](https://github.com/ota4j-team/opentest4j/blob/r1.3.0/LICENSE) |
| API Guardian | 1.1.2 | [Apache-2.0](https://github.com/apiguardian-team/apiguardian/blob/r1.1.2/LICENSE) |
