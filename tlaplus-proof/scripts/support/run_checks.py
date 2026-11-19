#!/usr/bin/env python3
"""Run SANY/TLC with isolated inputs, resource limits, and machine-readable evidence.

Examples (paths may be absolute or relative to this script):
  python3 run_checks.py sany --java /path/to/java
  python3 run_checks.py bfs T1_I1.cfg --timeout 60
  python3 run_checks.py simulate T3_I6_sim.cfg --seed 20261116 \
      --traces-per-worker 50 --depth 100 --workers 1 --timeout 20

JAVA (executable), JAVA_HOME, JAR, and TLA2TOOLS_JAR are supported. TLC's
simulation trace limit is per worker in the bundled 2026.09.25 tool: four
workers and --traces-per-worker 1000 request 4000 traces per seed. A fixed seed
and worker count repeat the random streams; concurrent scheduling can change
which counterexample is reported first. Use --workers 1 for strict replay.
"""

import argparse
import datetime as dt
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time
import uuid


HERE = Path(__file__).resolve().parent
GOOD = {"syntax_ok", "exhaustive_ok", "simulation_ok", "prepared"}
STOP_SIGNAL = None


def utc_now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def positive(value):
    number = int(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be a positive integer")
    return number


def positive_float(value):
    number = float(value)
    if not number > 0 or number == float("inf"):
        raise argparse.ArgumentTypeError("must be finite and greater than zero")
    return number


def locate_file(value, suffix=None):
    path = Path(value).expanduser()
    if suffix and not path.suffix:
        path = path.with_suffix(suffix)
    for candidate in (path, HERE / path):
        if candidate.is_file():
            return candidate.resolve()
    raise ValueError("file not found: " + str(path))


def locate_jar(value):
    explicit = value or os.environ.get("JAR") or os.environ.get("TLA2TOOLS_JAR")
    if explicit:
        return locate_file(explicit)
    bases = [HERE, *HERE.parents, Path.cwd(), *Path.cwd().parents]
    for base in dict.fromkeys(bases):
        for relative in ("tla2tools.jar", "toolkit/tla2tools.jar", "tools/tla2tools.jar"):
            candidate = base / relative
            if candidate.is_file():
                return candidate.resolve()
    raise ValueError("tla2tools.jar not found; supply --jar or JAR")


def locate_java(value):
    explicit = value or os.environ.get("JAVA")
    if not explicit and os.environ.get("JAVA_HOME"):
        explicit = str(Path(os.environ["JAVA_HOME"]) / "bin/java")
    executable = shutil.which(explicit or "java")
    if not executable:
        raise ValueError("Java executable not found; supply --java or JAVA")
    return str(Path(executable).resolve())


def sha256(path):
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(path)


def disk_bytes(root):
    """Logical bytes, including sparse files; errs conservatively for disk safety."""
    total = 0
    for directory, _, filenames in os.walk(root):
        for name in filenames:
            try:
                total += (Path(directory) / name).stat().st_size
            except FileNotFoundError:
                pass
    return total


def terminate_group(process):
    """The child owns its session; terminate its descendants as well as Java."""
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    try:
        os.killpg(process.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    process.wait()


def handle_signal(number, _frame):
    global STOP_SIGNAL
    STOP_SIGNAL = number


def last_integer(pattern, text):
    matches = re.findall(pattern, text, re.MULTILINE)
    return int(matches[-1].replace(",", "")) if matches else None


def parse_output(text):
    stats = {}
    patterns = {
        "states_generated": r"([\d,]+) states generated",
        "distinct_states": r"([\d,]+) distinct states found",
        "states_on_queue": r"([\d,]+) states left on queue",
        "search_depth": r"The depth of the complete state graph search is ([\d,]+)",
        "progress_depth": r"^Progress\(([\d,]+)\)",
        "states_checked": r"([\d,]+) states checked",
        "traces_generated": r"([\d,]+) traces generated",
        "simulation_states_generated": r"The number of states generated: ([\d,]+)",
    }
    for name, pattern in patterns.items():
        result = last_integer(pattern, text)
        if result is not None:
            stats[name] = result
    return stats


def runtime_parameters(text):
    """BFS fingerprint polynomial and seed must be preserved when recovering."""
    match = re.search(r"with fp (\d+) and seed (-?\d+)", text)
    return {"fp": int(match[1]), "seed": int(match[2])} if match else {}


def recovery_input(value, jar, workers):
    """Find a stopped run and verify its immutable inputs before reuse."""
    requested = Path(value).expanduser().resolve()
    directory = requested.parent if requested.is_file() else requested
    run_dir = next((parent for parent in (directory, *directory.parents)
                    if (parent / "result.json").is_file() and (parent / "input").is_dir()), None)
    if run_dir is None:
        raise ValueError("--recover must identify an existing run or its checkpoint directory")
    manifest = run_dir / "result.json"
    metadata = json.loads(manifest.read_text(encoding="utf-8"))
    if metadata.get("mode") != "bfs" or metadata.get("outcome") == "running":
        raise ValueError("recovery requires a stopped BFS run")
    if metadata["resources"]["workers"] != workers:
        raise ValueError("recovery requires the previous worker count: " + str(metadata["resources"]["workers"]))
    if metadata["toolkit"]["sha256"] != sha256(jar):
        raise ValueError("recovery requires the identical TLC jar (SHA256 differs)")
    for name, record in metadata["inputs"].items():
        path = run_dir / "input" / name
        if not path.is_file() or sha256(path) != record["sha256"]:
            raise ValueError("recovery input was changed or is missing: " + str(path))
    candidates = [directory] if (directory / "queue.chkpt").is_file() else sorted(
        {path.parent for path in (run_dir / "states").rglob("queue.chkpt")})
    candidates = [path for path in candidates if (path / "vars.chkpt").is_file()]
    if len(candidates) != 1:
        raise ValueError("expected one complete checkpoint directory; found " + str(len(candidates)))
    log = (run_dir / "output.log").read_text(encoding="utf-8", errors="replace")
    parameters = metadata.get("tlc_runtime") or runtime_parameters(log)
    if "fp" not in parameters or "seed" not in parameters:
        raise ValueError("could not determine prior TLC fingerprint polynomial and seed")
    return {"run_directory": str(run_dir), "result_sha256": sha256(manifest),
            "checkpoint_directory": str(candidates[0]), "tlc_runtime": parameters,
            "model": metadata["model"], "config": metadata["config"]}


def classify(mode, text, returncode, termination_reason, expected_traces=None):
    invariant = re.search(r"Invariant\s+([^\s]+)\s+is violated", text)
    if invariant:
        return "invariant_failure", invariant.group(1)
    if "Temporal properties were violated" in text or "Temporal property is violated" in text:
        return "temporal_failure", None
    if "Deadlock reached" in text:
        return "deadlock", None
    if termination_reason:
        return termination_reason, None
    errors = re.search(r"(?im)(?:^Error:|^\s*\*+\s*Errors?\s*:|Exception in thread|java\.lang\.[A-Za-z]*Error|^Fatal errors)", text)
    if returncode != 0 or errors:
        return "tool_error", None
    if mode == "sany":
        return ("syntax_ok" if "Semantic processing of module " in text else "incomplete"), None
    if mode == "bfs":
        complete = "Model checking completed. No error has been found." in text
        return ("exhaustive_ok" if complete else "incomplete"), None
    stats = parse_output(text)
    complete = "Finished in " in text and "Simulation using seed " in text
    # Require the observed finite trace budget, rather than treating exit 0 alone
    # (or an externally stopped simulator) as completed simulation.
    if complete and stats.get("traces_generated", 0) >= expected_traces:
        return "simulation_ok", None
    return "incomplete", None


def run_once(args, model, config, jar, java, seed):
    label = args.name or (config.stem if config else model.stem)
    label = re.sub(r"[^A-Za-z0-9_.-]+", "-", label).strip(".-")[:80] or "run"
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    suffix = "-seed" + str(seed) if seed is not None else ""
    run_dir = args.output.resolve() / (stamp + "-" + args.mode + "-" + label + suffix + "-" + uuid.uuid4().hex[:8])
    run_dir.mkdir(parents=True, exist_ok=False)
    input_dir = run_dir / "input"
    input_dir.mkdir()
    # Snapshot all adjacent modules so scenario EXTENDS references remain stable
    # even if the working model is subsequently edited during a long run.
    sources = list(model.parent.glob("*.tla"))
    if config:
        sources.append(config)
    inputs = {}
    for source in sources:
        target = input_dir / source.name
        shutil.copy2(source, target)
        inputs[source.name] = {"source": str(source), "sha256": sha256(target), "bytes": target.stat().st_size}
    for child in ("states", "traces", "tmp"):
        (run_dir / child).mkdir()
    recovery = args.recovery
    if recovery:
        checkpoint = Path(recovery["checkpoint_directory"])
        copied_checkpoint = run_dir / "states" / "recovered"
        if disk_bytes(checkpoint) + disk_bytes(run_dir) >= args.max_disk_gb * 1024 ** 3:
            raise ValueError("checkpoint copy exceeds --max-disk-gb; raise this run's disk budget")
        if not args.dry_run:
            shutil.copytree(checkpoint, copied_checkpoint)
        recovery = dict(recovery, copied_checkpoint_directory=str(copied_checkpoint),
                        checkpoint_handling="independent copy; source run is preserved")
    command = [java, "-XX:+UseParallelGC", "-XX:ActiveProcessorCount=" + str(args.workers), "-Xmx" + args.heap,
               "-Djava.io.tmpdir=" + str(run_dir / "tmp"), "-cp", str(jar)]
    if args.mode == "sany":
        command += ["tla2sany.SANY", model.name]
    else:
        command += ["tlc2.TLC", "-workers", str(args.workers), "-config", config.name,
                    "-metadir", str(run_dir / "states"), "-teSpecOutDir", str(run_dir / "traces")]
        if args.coverage is not None:
            command += ["-coverage", str(math.ceil(args.coverage / 60))]
        if args.checkpoint is not None:
            command += ["-checkpoint", str(args.checkpoint)]
        if args.action_graph:
            command += ["-dump", "dot,actionlabels", str(run_dir / "actions")]
        if recovery:
            command += ["-recover", recovery["copied_checkpoint_directory"],
                        "-fp", str(recovery["tlc_runtime"]["fp"]),
                        "-seed", str(recovery["tlc_runtime"]["seed"])]
        if args.mode == "simulate":
            command += ["-simulate", "num=" + str(args.traces_per_worker), "-depth", str(args.depth), "-seed", str(seed)]
        command += [model.name]
    expected = args.workers * args.traces_per_worker if args.mode == "simulate" else None
    metadata = {
        "schema_version": 2, "mode": args.mode, "outcome": "running", "started_utc": utc_now(),
        "run_directory": str(run_dir), "working_directory": str(input_dir), "command": command,
        "command_shell": shlex.join(command), "inputs": inputs,
        "model": model.name, "config": config.name if config else None,
        "toolkit": {"path": str(jar), "sha256": sha256(jar)},
        "resources": {"workers": args.workers, "heap": args.heap, "timeout_seconds": args.timeout,
                      "max_disk_gb": args.max_disk_gb, "disk_accounting": "logical bytes; sampled every 2 seconds"},
        "instrumentation": {"coverage_requested_seconds": args.coverage,
                            "coverage_effective_seconds": 60 * math.ceil(args.coverage / 60) if args.coverage is not None else None,
                            "checkpoint_minutes": args.checkpoint, "action_graph": args.action_graph},
        "recovery": recovery,
        "simulation": {"seed": seed, "depth": args.depth, "traces_per_worker": args.traces_per_worker,
                       "expected_total_traces": expected, "trace_budget_semantics": "per worker in bundled TLC 2026.09.25"} if seed is not None else None,
        "interpretation": "SANY syntax/semantic analysis only" if args.mode == "sany" else
            ("Finite bounded state space; constraints and symmetry in the configuration apply" if args.mode == "bfs" else
             "Finite random simulation; this cannot establish exhaustive safety or a mathematical proof"),
    }
    manifest = run_dir / "result.json"
    if args.dry_run:
        metadata["outcome"] = "prepared"
        write_json(manifest, metadata)
        print(str(manifest), flush=True)
        print(metadata["command_shell"], flush=True)
        return "prepared"
    write_json(manifest, metadata)
    print("Started " + args.mode + ": " + str(run_dir), flush=True)
    start = time.monotonic()
    termination = None
    process = None
    returncode = None
    next_disk_check = start
    try:
        with (run_dir / "output.log").open("w", encoding="utf-8") as log:
            process = subprocess.Popen(command, cwd=input_dir, stdout=log, stderr=subprocess.STDOUT,
                                       stdin=subprocess.DEVNULL, start_new_session=True)
            metadata["pid"] = process.pid
            write_json(manifest, metadata)
            while process.poll() is None:
                now = time.monotonic()
                if STOP_SIGNAL is not None:
                    termination = "interrupted"
                    break
                if now - start >= args.timeout:
                    termination = "timeout"
                    break
                if now >= next_disk_check:
                    used = disk_bytes(run_dir)
                    metadata["disk_bytes_last_sample"] = used
                    if used >= args.max_disk_gb * 1024 ** 3:
                        termination = "disk_limit"
                        break
                    next_disk_check = now + 2
                time.sleep(0.2)
            if termination:
                terminate_group(process)
            returncode = process.wait()
    except (OSError, KeyboardInterrupt) as error:
        termination = "interrupted" if isinstance(error, KeyboardInterrupt) else "launch_error"
        metadata["runner_error"] = str(error)
    finally:
        if process is not None and process.poll() is None:
            terminate_group(process)
        if process is not None:
            returncode = process.returncode
        log_path = run_dir / "output.log"
        text = log_path.read_text(encoding="utf-8", errors="replace") if log_path.exists() else ""
        outcome, failed_invariant = classify(args.mode, text, returncode, termination, expected)
        metadata.update({"outcome": outcome, "returncode": returncode, "termination_reason": termination,
                         "ended_utc": utc_now(), "elapsed_seconds": round(time.monotonic() - start, 3),
                         "stats": parse_output(text), "failed_invariant": failed_invariant,
                         "disk_bytes_final": disk_bytes(run_dir), "signal": STOP_SIGNAL})
        version = re.search(r"^TLC2? Version[^\n]*", text, re.MULTILINE)
        if version:
            metadata["toolkit"]["reported_version"] = version.group(0)
        metadata["tlc_runtime"] = runtime_parameters(text)
        metadata["checkpoints"] = [str(path.parent) for path in (run_dir / "states").rglob("queue.chkpt")
                                   if (path.parent / "vars.chkpt").is_file()]
        write_json(manifest, metadata)
    print(outcome + ": " + str(manifest), flush=True)
    return outcome


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=("sany", "bfs", "simulate"))
    parser.add_argument("config_file", nargs="?", help="TLC .cfg file (bfs/simulate)")
    parser.add_argument("--config", dest="config_option", help="alternative to the positional .cfg")
    parser.add_argument("--model", "--module", default="TRaftPaper.tla", help="main .tla module or path, optionally without suffix")
    parser.add_argument("--jar", "--tool", help="tla2tools.jar (otherwise JAR/TLA2TOOLS_JAR or auto detected)")
    parser.add_argument("--java", help="Java executable (otherwise JAVA/JAVA_HOME or PATH)")
    parser.add_argument("--workers", type=positive, default=1)
    parser.add_argument("--heap", default="1g", help="Java maximum heap (at most 2g)")
    parser.add_argument("--timeout", type=positive_float, default=20, help="seconds per run (at most 60)")
    parser.add_argument("--max-disk-gb", type=positive_float, default=0.25, help="stop at the logical GiB limit (at most 0.25)")
    parser.add_argument("--output", "--out", type=Path, default=HERE / "runs")
    parser.add_argument("--name", help="optional label in the unique run directory name")
    parser.add_argument("--seed", type=int, default=20261019)
    parser.add_argument("--seeds", help="comma-separated seeds; run sequentially")
    parser.add_argument("--repeat", type=positive, default=1, help="repeat with seed, seed+1, ... (alternative to --seeds)")
    parser.add_argument("--traces-per-worker", "--traces", type=positive, default=50)
    parser.add_argument("--depth", type=positive, default=100)
    parser.add_argument("--coverage", type=positive, metavar="SECONDS", help="coverage report interval; rounded up to whole minutes required by TLC")
    parser.add_argument("--checkpoint", type=positive, metavar="MINUTES", help="BFS checkpoint interval in whole minutes")
    parser.add_argument("--recover", type=Path, help="resume a stopped BFS run using its verified inputs and a copied checkpoint")
    parser.add_argument("--action-graph", action="store_true", help="write DOT transitions with action labels (diagnostics only; may be very large)")
    parser.add_argument("--dry-run", action="store_true", help="snapshot inputs and record command without launching Java")
    args = parser.parse_args()
    if not re.fullmatch(r"[1-9]\d*[kKmMgG]", args.heap):
        parser.error("--heap must be a positive integer followed by k, m or g")
    heap_bytes = int(args.heap[:-1]) * {"k": 1024, "m": 1024**2, "g": 1024**3}[args.heap[-1].lower()]
    if args.workers > 2 or heap_bytes > 2 * 1024**3 or args.timeout > 60 or args.max_disk_gb > 0.25:
        parser.error("Current review is limited to 2 workers, 2 GiB heap, 60 seconds and 0.25 GiB per run")
    if args.config_file and args.config_option:
        parser.error("provide either positional config or --config")
    if args.mode != "sany" and not (args.config_file or args.config_option or args.recover):
        parser.error("bfs and simulate require a .cfg file")
    if args.mode == "sany" and (args.config_file or args.config_option):
        parser.error("SANY does not read a TLC configuration")
    if args.seeds and args.repeat != 1:
        parser.error("--seeds and --repeat cannot be combined")
    if args.mode != "bfs" and (args.recover or args.checkpoint or args.action_graph):
        parser.error("--recover, --checkpoint and --action-graph require bfs")
    if args.mode == "sany" and args.coverage:
        parser.error("--coverage requires bfs or simulate")
    try:
        jar, java = locate_jar(args.jar), locate_java(args.java)
        args.recovery = recovery_input(args.recover, jar, args.workers) if args.recover else None
        if args.recovery:
            if args.config_file or args.config_option or args.model != "TRaftPaper.tla":
                raise ValueError("--recover obtains model/config from the original run; omit --model and the config argument")
            original_input = Path(args.recovery["run_directory"]) / "input"
            model = original_input / args.recovery["model"]
            config = original_input / args.recovery["config"]
        else:
            model = locate_file(args.model, ".tla")
            config = locate_file(args.config_file or args.config_option, ".cfg") if args.mode != "sany" else None
        seeds = [int(seed.strip()) for seed in args.seeds.split(",")] if args.seeds else list(range(args.seed, args.seed + args.repeat))
        if any(seed < -(2 ** 63) or seed >= 2 ** 63 for seed in seeds):
            raise ValueError("simulation seeds must fit a signed 64-bit integer")
    except (ValueError, OSError, KeyError) as error:
        parser.error(str(error))
    signal.signal(signal.SIGTERM, handle_signal)
    signal.signal(signal.SIGINT, handle_signal)
    outcomes = []
    for seed in seeds if args.mode == "simulate" else [None]:
        if STOP_SIGNAL is not None:
            break
        try:
            outcomes.append(run_once(args, model, config, jar, java, seed))
        except (ValueError, OSError) as error:
            parser.error(str(error))
        if outcomes[-1] not in GOOD:
            break
    if STOP_SIGNAL is not None:
        return 128 + STOP_SIGNAL
    return 0 if outcomes and all(outcome in GOOD for outcome in outcomes) else 1


if __name__ == "__main__":
    sys.exit(main())
