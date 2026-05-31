"""
RECTANGLE Cipher Differential Cryptanalysis
Main entry point for running differential attacks on RECTANGLE.

Usage:
    # 相关密钥差分分析（默认模式）
    python main.py --mode related-key --rounds 8
    python main.py --mode related-key --rounds 8-12

    # 最小活跃S盒搜索
    python main.py --mode active-sbox --rounds 8
    python main.py --mode active-sbox --rounds 1-10

    # 显示模式（0: 无输出, 1: 简洁输出, 2: 详细输出）
    python main.py --mode related-key --rounds 8 --show-mode 2

    # 设置权重起始值（用于优化搜索）
    python main.py --mode related-key --rounds 10 --start-weight 15

    # 设置输出目录（结果保存到指定文件夹，不存在则自动创建）
    python main.py --mode related-key --rounds 8 --output-dir my_results
    python main.py --mode active-sbox --rounds 8 --output-dir sbox_analysis

    # 其他选项
    python main.py --version 64_128 --solver Cadical195
    python main.py --help
"""
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))

import argparse
from primitives.rectangle import RECTANGLE_BLOCKCIPHER
from attacks.attacks import diff_attacks


def parse_round_range(rounds_str):
    """
    解析轮数参数，支持单个值或范围。

    Args:
        rounds_str: 轮数字符串，如 "8" 或 "8-12"

    Returns:
        (start, end) 元组
    """
    if '-' in str(rounds_str):
        parts = str(rounds_str).split('-')
        if len(parts) != 2:
            raise argparse.ArgumentTypeError("轮数范围格式错误，应为 'start-end'，如 '8-12'")
        start, end = int(parts[0]), int(parts[1])
        if start > end:
            raise argparse.ArgumentTypeError(f"起始轮数 {start} 大于结束轮数 {end}")
        return start, end
    else:
        r = int(rounds_str)
        return r, r


def get_output_dir(output_dir_name):
    """
    获取输出目录的绝对路径。

    Args:
        output_dir_name: 输出目录名称

    Returns:
        Path 对象，指向 files/{output_dir_name}
    """
    if output_dir_name is None:
        return None

    script_dir = Path(__file__).resolve().parent
    output_path = script_dir / "files" / output_dir_name
    output_path.mkdir(parents=True, exist_ok=True)
    return output_path


def run_single_analysis(rounds, version, mode, show_mode, start_weight, solver, output_dir):
    """
    运行单轮数差分分析。

    Args:
        rounds: 加密轮数
        version: 密码版本 [64, 80] 或 [64, 128]
        mode: 分析模式 ('related-key' 或 'active-sbox')
        show_mode: 显示模式 (0, 1, 2)
        start_weight: 起始权重值（用于 AT LEAST 优化）
        solver: SAT求解器名称
        output_dir: 输出目录名称（相对于 files/）
    """
    cipher = RECTANGLE_BLOCKCIPHER(r=rounds, version=version)

    # 根据模式设置约束和目标
    if mode == 'related-key':
        constraints = ['INPUT_NOT_ZERO', 'KEY_NOT_ZERO']
        goal = 'DIFFERENTIALPATH_PROB'
        mode_desc = 'Related-Key Differential Analysis'
    else:  # active-sbox
        constraints = ['INPUT_NOT_ZERO']
        goal = 'DIFFERENTIAL_SBOXCOUNT'
        mode_desc = 'Minimum Active S-box Analysis'

    # 设置目标函数
    if start_weight is not None and start_weight > 0:
        objective_target = f'AT LEAST {start_weight}'
    else:
        objective_target = 'OPTIMAL'

    # 构建 config_model
    config_model = {'model_type': 'sat'}
    if output_dir:
        config_model['output_dir'] = str(output_dir)

    print(f"\n{'=' * 60}")
    print(f"RECTANGLE Differential Analysis")
    print(f"{'=' * 60}")
    print(f"Cipher: {cipher.name}")
    print(f"Mode: {mode_desc}")
    print(f"Rounds: {rounds}")
    print(f"Goal: {goal}")
    print(f"Constraints: {constraints}")
    print(f"Objective: {objective_target}")
    print(f"Show Mode: {show_mode}")
    print(f"Solver: {solver}")
    if output_dir:
        print(f"Output Dir: {output_dir}")
    print(f"{'=' * 60}\n")

    trails = diff_attacks(
        cipher,
        goal=goal,
        constraints=constraints,
        objective_target=objective_target,
        show_mode=show_mode,
        config_model=config_model,
        config_solver={'solver': solver},
    )

    if trails:
        t = trails[0]
        weight = t.data.get('diff_weight')
        round_weights = t.data.get('rounds_diff_weight', [])

        print(f"\n{'=' * 60}")
        print(f"Result: FOUND")
        print(f"Total Weight: {weight}")

        if round_weights:
            print(f"Round Weights: {round_weights}")

        if goal == 'DIFFERENTIALPATH_PROB':
            prob = 2 ** (-weight) if weight else 1.0
            print(f"Probability: {prob:.2e}")
        else:
            print(f"Active S-boxes: {int(weight) if weight else 'N/A'}")

        print(f"{'=' * 60}\n")
    else:
        print(f"\n{'=' * 60}")
        print(f"Result: NOT FOUND (UNSAT or timeout)")
        print(f"{'=' * 60}\n")

    return trails


def run_multi_round(start, end, version, mode, show_mode, solver, output_dir):
    """
    运行渐进式多轮分析，从 start 轮逐步搜索到 end 轮。

    Args:
        start: 起始轮数
        end: 结束轮数
        version: 密码版本 [64, 80] 或 [64, 128]
        mode: 分析模式 ('related-key' 或 'active-sbox')
        show_mode: 显示模式 (0, 1, 2)
        solver: SAT求解器名称
        output_dir: 输出目录名称（相对于 files/）
    """
    if mode == 'related-key':
        constraints = ['INPUT_NOT_ZERO', 'KEY_NOT_ZERO']
        goal = 'DIFFERENTIALPATH_PROB'
        mode_desc = 'Related-Key Differential Analysis'
        result_label = 'Weight'
    else:  # active-sbox
        constraints = ['INPUT_NOT_ZERO']
        goal = 'DIFFERENTIAL_SBOXCOUNT'
        mode_desc = 'Minimum Active S-box Analysis'
        result_label = 'Active S-boxes'

    print(f"\n{'=' * 60}")
    print(f"Multi-Round Progressive Analysis")
    print(f"Mode: {mode_desc}")
    print(f"Version: {'64/128' if version == [64, 128] else '64/80'}")
    print(f"Rounds: {start} to {end}")
    print(f"Goal: {goal}")
    print(f"Constraints: {constraints}")
    print(f"Show Mode: {show_mode}")
    if output_dir:
        print(f"Output Dir: {output_dir}")
    print(f"{'=' * 60}\n")

    results = []
    for r in range(start, end + 1):
        cipher = RECTANGLE_BLOCKCIPHER(r=r, version=version)
        print(f"\n--- Round {r} ---")

        # 构建 config_model
        config_model = {'model_type': 'sat'}
        if output_dir:
            config_model['output_dir'] = str(output_dir)

        trails = diff_attacks(
            cipher,
            goal=goal,
            constraints=constraints,
            objective_target='OPTIMAL',
            show_mode=show_mode,
            config_model=config_model,
            config_solver={'solver': solver},
        )

        if trails:
            weight = trails[0].data.get('diff_weight')
            results.append((r, weight))
            print(f"  {result_label}: {weight}")
        else:
            results.append((r, None))
            print(f"  NOT FOUND")

    # 打印汇总表
    print(f"\n{'=' * 60}")
    print(f"Summary ({mode_desc}):")
    print(f"{'-' * 40}")
    print(f"{'Rounds':<10} | {result_label}")
    print(f"{'-' * 40}")
    for r, w in results:
        status = f"{w}" if w is not None else "UNSAT"
        print(f"{r:<10} | {status}")
    print(f"{'=' * 60}\n")

    return results


def main():
    """
    主函数：解析命令行参数并执行差分分析。
    """
    parser = argparse.ArgumentParser(
        description='RECTANGLE Differential Cryptanalysis',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__
    )

    # 分析模式
    parser.add_argument('--mode', '-m', choices=['related-key', 'active-sbox'],
                       default='related-key',
                       help='分析模式: related-key (相关密钥差分) 或 active-sbox (最小活跃S盒), 默认: related-key')

    # 轮数参数，支持单个值或范围
    parser.add_argument('--rounds', '-r', type=str, default='6',
                       help='加密轮数，支持单个值(如 8)或范围(如 8-12), 默认: 6')

    # 密码版本
    parser.add_argument('--version', '-v', choices=['64_80', '64_128'],
                       default='64_80',
                       help='密码版本: 64_80 (64位块/80位密钥) 或 64_128 (64位块/128位密钥), 默认: 64_80')

    # 显示模式
    parser.add_argument('--show-mode', '-s', type=int, choices=[0, 1, 2, 3],
                       default=0,
                       help='显示模式: 0=无输出, 1=简洁输出, 2=详细输出, 3=完整输出, 默认: 0')

    # 起始权重值（用于优化搜索）
    parser.add_argument('--start-weight', '-w', type=int, default=None,
                       help='起始权重值，设置为 AT LEAST 模式，可加速搜索, 默认: None (OPTIMAL模式)')

    # SAT求解器
    parser.add_argument('--solver', type=str, default='Cadical195',
                       help='SAT求解器名称, 默认: Cadical195')

    # 输出目录
    parser.add_argument('--output-dir', '-o', type=str, default=None,
                       help='输出目录名称（保存在 files/{name} 下，不存在则自动创建）, 默认: None')

    args = parser.parse_args()

    # 解析版本
    version = [64, 80] if args.version == '64_80' else [64, 128]

    # 解析轮数范围
    start_rounds, end_rounds = parse_round_range(args.rounds)

    # 获取输出目录
    output_dir = get_output_dir(args.output_dir)

    # 根据轮数范围选择执行单轮还是多轮分析
    if start_rounds == end_rounds:
        # 单轮分析
        run_single_analysis(
            rounds=start_rounds,
            version=version,
            mode=args.mode,
            show_mode=args.show_mode,
            start_weight=args.start_weight,
            solver=args.solver,
            output_dir=output_dir
        )
    else:
        # 多轮渐进分析
        run_multi_round(
            start=start_rounds,
            end=end_rounds,
            version=version,
            mode=args.mode,
            show_mode=args.show_mode,
            solver=args.solver,
            output_dir=output_dir
        )


if __name__ == '__main__':
    main()
