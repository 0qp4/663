# RECTANGLE 密钥差分密码分析

一个独立的 **基于 SAT 的 RECTANGLE 轻量级分组密码相关密钥差分密码分析框架**，支持 64/80 位和 64/128 位密钥版本。

## 目录

- [概述](#概述)
- [安装](#安装)
- [快速开始](#快速开始)
- [项目结构](#项目结构)
- [功能特性](#功能特性)
- [配置选项](#配置选项)
- [示例](#示例)
- [输出文件](#输出文件)
- [依赖项](#依赖项)

## 概述

RECTANGLE 是一款为资源受限环境设计的 64 位轻量级分组密码，支持两种密钥长度：
- **RECTANGLE-64/80**：64 位分组，80 位密钥（25 轮）
- **RECTANGLE-64/128**：64 位分组，128 位密钥（25 轮）

本项目提供了一套完整的基于 SAT 的差分密码分析实现，包括：

- 使用 SAT 求解器（Cadical、Lingeling、Glucose 等）进行差分路径搜索
- 使用 `KEY_NOT_ZERO` 约束进行**相关密钥差分分析**
- 最小活跃 S 盒计数，用于测量传播特性
- 1 到 25+ 轮的多轮分析
- 两种 RECTANGLE 版本：64/80 位和 64/128 位密钥

## 安装

### 前置要求

1. **Python 3.8+**
2. **SAT 求解器**（推荐：Cadical）

### 安装 Cadical

Cadical 是推荐的 SAT 求解器后端：

```bash
# 克隆仓库
git clone https://github.com/arminbiere/cadical.git
cd cadical

# 编译 Cadical
mkdir build && cd build
cmake ..
make

# 安装（可选，或添加到 PATH）
sudo make install
```

或者从发布页面下载预编译二进制文件。

### 安装 Python 依赖

```bash
cd RECTANGLE
pip install -r requirements.txt
```

## 快速开始

### 基本的差分路径搜索

```python
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))

from primitives.rectangle import RECTANGLE_BLOCKCIPHER
from attacks.attacks import diff_attacks

# 创建 4 轮 RECTANGLE-64/80 密码器
cipher = RECTANGLE_BLOCKCIPHER(r=4, version=[64, 80])

# 搜索最优差分路径
trails = diff_attacks(
    cipher,
    goal='DIFFERENTIALPATH_PROB',
    constraints=['INPUT_NOT_ZERO'],
    objective_target='OPTIMAL',
    config_model={'model_type': 'sat'},
    config_solver={'solver': 'Cadical195'},
)

if trails:
    print(f"权重: {trails[0].data['diff_weight']}")
    print(f"概率: {2**(-trails[0].data['diff_weight']):.6e}")
```

### 相关密钥差分分析

```python
cipher = RECTANGLE_BLOCKCIPHER(r=8, version=[64, 80])

trails = diff_attacks(
    cipher,
    goal='DIFFERENTIALPATH_PROB',
    constraints=['INPUT_NOT_ZERO', 'KEY_NOT_ZERO'],  # KEY_NOT_ZERO 是密钥约束
    objective_target='OPTIMAL',
    config_model={'model_type': 'sat'},
    config_solver={'solver': 'Cadical195'},
)
```

### 使用命令行界面

```bash
# 基本分析（6 轮，64/80）
python main.py

# 带相关密钥约束
python main.py --rounds 10 --key-diff

# 多轮搜索
python main.py --multi-round 1 15

# 计数最小活跃 S 盒
python main.py --sbox-count --rounds 8

# 64/128 密钥版本
python main.py --version 64_128 --rounds 6
```

## 项目结构

```
RECTANGLE/
├── primitives/              # 密码算法定义
│   ├── __init__.py
│   ├── primitives.py        # 基类（Block_cipher、Permutation 等）
│   └── rectangle.py        # RECTANGLE 密码算法实现
├── operators/               # 密码学算子
│   ├── __init__.py
│   ├── Sbox.py             # S 盒算子，含 DDT/SAT 建模
│   ├── boolean_operators.py # XOR、AND、OR、NOT、ConstantXOR
│   ├── modular_operators.py # ModAdd、ModMul、ConstantAdd
│   ├── matrix.py           # 矩阵运算
│   └── operators.py         # 基算子类
├── variables/               # 变量建模
│   ├── __init__.py
│   └── variables.py         # 密码算法建模用的变量类
├── attacks/                 # 攻击实现
│   ├── __init__.py
│   ├── attacks.py           # 高级攻击接口（diff_attacks）
│   ├── differential_cryptanalysis.py  # 核心差分分析
│   └── attack_trace.py      # 路径数据结构
├── tools/                   # 辅助工具
│   ├── __init__.py
│   ├── sat_search.py        # 基于 SAT 的搜索策略
│   ├── milp_search.py      # 基于 MILP 的搜索（可选）
│   ├── model_constraints.py # 约束生成工具
│   ├── model_objective.py   # 目标函数处理
│   ├── minimize_logic.py    # 逻辑极小化（Espresso）
│   ├── polyhedron.py       # 多面体运算
│   └── resource_monitor.py  # 运行时资源监控
├── solving/                 # 求解器接口
│   ├── __init__.py
│   └── solving.py           # SAT/MILP 求解器包装器（pysat）
├── visualisations/           # 可视化（可选）
│   ├── __init__.py
│   └── visualisations.py
├── files/                    # 输出文件（自动创建）
│   ├── sbox_modeling/       # S 盒约束模型
│   └── *.cnf, *.json, *.txt # 生成的 分析结果
├── examples/                 # 示例脚本
│   ├── example_1_basic_differential.py
│   ├── example_2_related_key.py
│   ├── example_3_active_sbox.py
│   ├── example_4_multi_round.py
│   └── example_5_64_128_version.py
├── logs/                     # 求解器日志（自动创建）
├── main.py                   # 命令行入口
├── __init__.py
├── requirements.txt
├── README.md
└── .gitignore
```

## 功能特性

### 1. 差分路径搜索

搜索权重最小（概率最大）的最优差分路径：

```python
trails = diff_attacks(
    cipher,
    goal='DIFFERENTIALPATH_PROB',
    constraints=['INPUT_NOT_ZERO'],
    objective_target='OPTIMAL',
    config_model={'model_type': 'sat'},
    config_solver={'solver': 'Cadical195'},
)
```

### 2. 相关密钥差分分析

当密钥差分非零时分析差分。这是相关密钥密码分析的**核心功能**：

```python
# KEY_NOT_ZERO 约束强制至少有一个密钥位不同
trails = diff_attacks(
    cipher,
    goal='DIFFERENTIALPATH_PROB',
    constraints=['INPUT_NOT_ZERO', 'KEY_NOT_ZERO'],
    objective_target='OPTIMAL',
    config_model={'model_type': 'sat'},
    config_solver={'solver': 'Cadical195'},
)
```

### 3. 活跃 S 盒计数

计数最小活跃 S 盒数量，用于衡量对差分攻击的抵抗力：

```python
trails = diff_attacks(
    cipher,
    goal='DIFFERENTIAL_SBOXCOUNT',
    constraints=['INPUT_NOT_ZERO'],
    objective_target='OPTIMAL',
    config_model={'model_type': 'sat'},
    config_solver={'solver': 'Cadical195'},
)
```

### 4. 多轮递进搜索

从第 1 轮到第 N 轮递进搜索：

```bash
python main.py --multi-round 1 15
```

## 配置选项

### 密码算法版本

```python
# RECTANGLE-64/80（64 位分组，80 位密钥）
cipher = RECTANGLE_BLOCKCIPHER(r=10, version=[64, 80])

# RECTANGLE-64/128（64 位分组，128 位密钥）
cipher = RECTANGLE_BLOCKCIPHER(r=10, version=[64, 128])
```

### SAT 求解器选项

| 求解器 | 描述 |
|--------|------|
| `Cadical195` | 推荐，开源 |
| `Cadical153` | 替代 Cadical 版本 |
| `Lingeling` | 性能强劲 |
| `Glucose4` | 带胶水启发式的 Glucose |
| `Minisat22` | 经典 SAT 求解器 |

### 搜索目标

| 目标 | 描述 |
|------|------|
| `DIFFERENTIALPATH_PROB` | 找到权重最小的路径（最大概率） |
| `DIFFERENTIAL_SBOXCOUNT` | 找到活跃 S 盒最少的路径 |
| `DIFFERENTIAL_PROB` | 在固定输入/输出下搜索差分 |

### 约束条件

| 约束 | 描述 |
|------|------|
| `INPUT_NOT_ZERO` | 强制明文差分非零 |
| `KEY_NOT_ZERO` | 强制密钥差分非零（相关密钥分析） |

## 示例

### 示例 1：基本差分搜索

```bash
python examples/example_1_basic_differential.py
```

在 4 轮 RECTANGLE-64/80 上搜索最优差分路径。

### 示例 2：相关密钥分析

```bash
python examples/example_2_related_key.py
```

在相关密钥设置下搜索密钥差分非零的差分路径。

### 示例 3：活跃 S 盒计数

```bash
python examples/example_3_active_sbox.py
```

计算 1-6 轮的最小活跃 S 盒数量。

### 示例 4：多轮分析

```bash
python examples/example_4_multi_round.py
```

从 1 到 6 轮的递进多轮分析。

### 示例 5：64/128 版本

```bash
python examples/example_5_64_128_version.py
```

比较两种 RECTANGLE 密钥版本。

## 输出文件

结果保存在 `files/` 目录中：

| 文件类型 | 描述 |
|----------|------|
| `*_sat_model.cnf` | SAT 求解器输入（CNF 格式） |
| `*_trail.json` | JSON 格式的路径数据 |
| `*_trail.txt` | 人类可读的路径输出 |

日志保存在 `logs/` 目录中。

## 依赖项

| 包 | 必需 | 用途 |
|---------|----------|------|
| numpy | 是 | 数值运算 |
| python-sat | 是 | SAT 求解器接口 |
| Cadical（二进制） | 推荐 | SAT 求解器后端 |
| psutil | 否 | 资源监控 |
| matplotlib | 否 | 可视化 |

## 参考文献

- RECTANGLE 密码算法：面向硬件的轻量级分组密码
  - Zhang 等，IEEE Transactions on Computers 2015

- 开放密码分析平台（OCP）
  - https://github.com/Open-CP/OCP

## 许可证

本项目源自开放密码分析平台（OCP）。有关许可详情请参阅原始 OCP 项目。

## 引用

如果您在研究中使用本项目，请引用：

```
RECTANGLE 密钥差分密码分析框架
https://github.com/your-repo/RECTANGLE
```
