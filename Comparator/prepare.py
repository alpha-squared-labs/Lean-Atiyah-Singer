"""Compile the three comparator modules and export their selected proof roots.

Existing accepted production dependencies are imported from the production .lake.
No dependency directories are copied and no Lake build traces are fabricated.
"""

import argparse
import json
import re
import subprocess
import time
import tomllib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODULES = ("Statements", "Challenge", "Solution")
TARGETS = [
    "AtiyahSinger.ComparatorTargets." + name
    for name in (
        "t01_atlas", "t01_native", "t02_atlas", "t02_native",
        "t03_atlas", "t03_native", "t04",
    )
]
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def option_args(options, prefix=""):
    """TOML dotted option keys parse as nested tables."""
    result = []
    for key, value in options.items():
        name = prefix + key
        if isinstance(value, dict):
            result.extend(option_args(value, name + "."))
        else:
            rendered = str(value).lower() if isinstance(value, bool) else str(value)
            result.append(f"-D{name}={rendered}")
    return result


def names_in_function(source, name):
    """Read the current bundled comparator's literal kernel target list."""
    match = re.search(r"(?ms)^def " + name + r"\b.*?(?=^def |\Z)", source)
    if match is None or "#[" not in match.group():
        raise ValueError(f"Unrecognized bundled comparator function: {name}")
    body = re.sub(r"--[^\n]*", "", match.group())
    arrays = re.findall(r"#\[(.*?)\]", body, re.S)
    return re.findall(r"``([A-Za-z_][A-Za-z_0-9.]*)", "\n".join(arrays))


def execute(command, output, label, records):
    started = time.monotonic()
    log = output / (label + ".log")
    with log.open("wb") as handle:
        result = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT)
    records.append({
        "step": label,
        "command": command,
        "exit_code": result.returncode,
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "log": str(log),
    })
    print(f"{label}: exit {result.returncode}", flush=True)
    if result.returncode != 0:
        raise RuntimeError(f"{label} failed; see {log}")


def prepare(output):
    config_source = (ROOT / "Comparator/config.json").read_bytes()
    lake_source = (ROOT / "lakefile.toml").read_bytes()
    config = json.loads(config_source)
    if (config["theorem_names"] != TARGETS or config["definition_names"] != []
            or config["permitted_axioms"] != AXIOMS
            or config["challenge_module"] != "Challenge"
            or config["solution_module"] != "Solution"
            or config["external_kernels"] != {"nanoda": ["nanoda_bin"]}):
        raise ValueError("Comparator configuration differs from the reviewed seven-target scope")
    output.mkdir(parents=True, exist_ok=False)
    sources = {name: (ROOT / "Comparator" / (name + ".lean")).read_bytes()
               for name in MODULES}
    for name, content in sources.items():
        (output / (name + ".lean")).write_bytes(content)
    (output / "config.json").write_bytes(config_source)
    (output / "lakefile.toml").write_bytes(lake_source)
    options = tomllib.loads(lake_source.decode())["leanOptions"]
    lean_args = option_args(options)
    lib = ROOT / ".lake/build/lib/lean"
    ir = ROOT / ".lake/build/ir"
    lib.mkdir(parents=True, exist_ok=True)
    ir.mkdir(parents=True, exist_ok=True)
    records = []
    receipt = {"status": "RUNNING", "targets": TARGETS, "runs": records}
    try:
        for name in MODULES:
            command = [
                "lake", "env", "lean", "--root=Comparator", f"Comparator/{name}.lean",
                "-o", str(lib / (name + ".olean")),
                "-i", str(lib / (name + ".ilean")),
                "-c", str(ir / (name + ".c")),
            ] + lean_args
            execute(command, output, "compile_" + name, records)
        prefix = Path(subprocess.check_output(
            ["lake", "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip())
        driver = prefix / "src/lean/lake/Lake/CLI/Check.lean"
        driver_source = driver.read_text()
        builtins = names_in_function(driver_source, "builtinTargets")
        primitives = names_in_function(driver_source, "primitiveTargets")
        if builtins != ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"]:
            raise ValueError("Unrecognized bundled quotient target list")
        if not primitives or "optParam" not in primitives or "outParam" not in primitives:
            raise ValueError("Incomplete bundled primitive target list")
        export_targets = builtins + TARGETS + AXIOMS + primitives
        for name in ("Challenge", "Solution"):
            command = ["lake", "env", str(prefix / "bin/leanexport"), name, "--"]
            command += export_targets
            started = time.monotonic()
            path = output / (name + ".ndjson")
            errors = output / ("export_" + name + ".log")
            with path.open("wb") as handle, errors.open("wb") as err:
                result = subprocess.run(command, cwd=ROOT, stdout=handle, stderr=err)
            records.append({
                "step": "export_" + name, "command": command,
                "exit_code": result.returncode,
                "elapsed_seconds": round(time.monotonic() - started, 3),
                "export": str(path), "log": str(errors),
            })
            print(f"export_{name}: exit {result.returncode}", flush=True)
            if result.returncode != 0:
                raise RuntimeError(f"Export of {name} failed; see {errors}")
        for name, content in sources.items():
            if (ROOT / "Comparator" / (name + ".lean")).read_bytes() != content:
                raise RuntimeError(f"Source changed during preparation: {name}")
            (output / (name + ".lean")).write_bytes(content)
        if (ROOT / "Comparator/config.json").read_bytes() != config_source:
            raise RuntimeError("Comparator configuration changed during preparation")
        if (ROOT / "lakefile.toml").read_bytes() != lake_source:
            raise RuntimeError("Lake options changed during preparation")
        receipt.update({
            "status": "PREPARED_NOT_YET_COMPARATOR_ACCEPTED",
            "source_snapshots": [name + ".lean" for name in MODULES],
            "sources_unchanged_during_preparation": True,
            "bundled_exporter": str(prefix / "bin/leanexport"),
            "definition_holes": [], "permitted_axioms": AXIOMS,
            "comparator_command": [
                "lake", "env", "lake", "comparator", "--config", str(output / "config.json"),
                "--challenge-from-export", str(output / "Challenge.ndjson"),
                "--solution-from-export", str(output / "Solution.ndjson"),
            ],
        })
    except BaseException:
        receipt["status"] = "FAILED"
        raise
    finally:
        (output / "preparation.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt["comparator_command"]), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True,
                        help="New evidence directory for source snapshots, logs and proof exports")
    prepare(parser.parse_args().output.resolve())
