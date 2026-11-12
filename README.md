# JustSimple

[![JDK 17+](https://img.shields.io/badge/JDK-17%2B-C2410C?style=flat-square)](docs/usage.md#构建)
[![Agent · Node.js 22.19.0+](https://img.shields.io/badge/Agent-Node.js%2022.19.0%2B-1B7F37?style=flat-square)](docs/usage.md#agent)
[![GPL-3.0-or-later](https://img.shields.io/badge/License-GPL--3.0--or--later-355C9A?style=flat-square)](LICENSE)

JustSimple 是一款面向 Java 反序列化风险的本地字节码审计工具。提供应用或组件的编译产物和目标类库，就可以顺着调用关系和数据来源排查风险，查看依据及成立条件。

## 工作流程

```mermaid
---
config:
  flowchart:
    rankSpacing: 28
    nodeSpacing: 22
    padding: 8
---
flowchart LR
    IN["输入<br/>目标 · 依赖 · JDK<br/>静态数据（可选）"]

    subgraph S["Scanner · 静态分析"]
        CORE["建立字节码索引<br/>分析调用与值来源<br/>整理证据和待查条件"]
    end

    subgraph B["Bridge · 结果查询"]
        PAGE["摘要与引用<br/>按页读证据"]
    end

    subgraph A["Agent · 交互审计"]
        BOARD["按需查证<br/>黑板记录"]
    end

    IN --> S
    S -->|"CLI"| SCAN["扫描报告<br/>JSON · Markdown"]
    S --> B
    B -->|"/scan-only"| SCAN
    B -->|"/agent"| A
    A --> AUDIT["审计报告<br/>快照 · 证据附件"]

    classDef input fill:#edf4ff,stroke:#5277a6,color:#193553
    classDef scanner fill:#eaf6ee,stroke:#528364,color:#1b402b
    classDef bridge fill:#eef0fc,stroke:#6879b5,color:#2f3c65
    classDef agent fill:#fff2df,stroke:#ae773c,color:#573816
    classDef output fill:#f2f5f8,stroke:#718295,color:#273748
    class IN input
    class CORE scanner
    class PAGE bridge
    class BOARD agent
    class SCAN,AUDIT output
```

## 项目特点

- **扫描可以独立运行。** Scanner 支持离线扫描和报告导出。想继续查证时，可在 Agent 终端使用同一套分析能力。
- **发现可以回查到字节码。** 报告保留相关指令和调用关系，也会说明缺少哪些条件、分析查到了哪里。
- **证据按需读取。** 终端先展示摘要，需要时再翻到具体指令或关系。

## 文档

[开始使用](docs/usage.md) · [架构](docs/architecture.md) · [交互审计](docs/reference/audit.md) · [Gleipner 评测](docs/evaluation.md)

[开发约束](AGENTS.md) · [第三方依赖许可](docs/THIRD_PARTY_NOTICES.md)
