"""Bazel rules for WAST-driven tests using synth-test native runner."""

load("@rules_renode//renode:defs.bzl", "renode_test")

def wast_test(
    name,
    wast,
    wat_src,
    platform = "//tests/renode:synth_cortex_m.repl",
    func_addr = "0x91",
    func_name = None,
    tags = [],
    **kwargs):
    """
    Run WAST tests against Synth-compiled ARM binary on Renode.

    This rule:
    1. Compiles the WAT source to ARM ELF using Synth
    2. Generates a Robot test file from the WAST using synth-test
    3. Runs the tests on Renode

    Args:
        name: Test target name
        wast: WAST file with test assertions
        wat_src: WAT source file to compile
        platform: Renode platform description file
        func_addr: Function address (with Thumb bit)
        func_name: Export name of function to compile (for multi-function modules)
        tags: Additional tags
        **kwargs: Additional arguments passed to renode_test
    """

    # Generate ELF from WAT
    elf_name = name + "_elf"

    # Build compile command with optional --func-name
    compile_cmd = "$(location //crates:synth) compile $(location {}) -o $@ --cortex-m".format(wat_src)
    if func_name:
        compile_cmd += " --func-name {}".format(func_name)

    native.genrule(
        name = elf_name,
        srcs = [wat_src],
        outs = [name + ".elf"],
        cmd = compile_cmd,
        tools = ["//crates:synth"],
    )

    # Generate Robot test from WAST
    robot_name = name + "_robot"

    # Build test generation command with optional --filter-func
    gen_cmd = "$(location //crates:synth-test) generate --wast $(location {}) --robot $@ --platform {} --func-addr {}".format(
        wast,
        "$$" + "{CURDIR}/" + platform.split(":")[-1] if ":" in platform else platform,
        func_addr
    )
    if func_name:
        gen_cmd += " --filter-func {}".format(func_name)

    native.genrule(
        name = robot_name,
        srcs = [wast],
        outs = [name + "_test.robot"],
        cmd = gen_cmd,
        tools = ["//crates:synth-test"],
    )

    # Run Renode test
    renode_test(
        name = name,
        robot_test = ":" + robot_name,
        deps = [platform] if not platform.startswith("//") else [],
        variables_with_label = {
            "ELF": ":" + elf_name,
        },
        tags = tags + ["wast"],
        **kwargs
    )


def wast_multi_func_test(
    name,
    wast,
    wat_src = None,
    platform = "//tests/renode:synth_cortex_m.repl",
    tags = [],
    **kwargs):
    """
    Run WAST tests against a multi-function Synth-compiled ARM binary on Renode.

    This rule:
    1. Compiles ALL exported functions from WAT source to ARM ELF using --all-exports
    2. Generates Robot test file with per-function addresses from ELF symbol table
    3. Runs the tests on Renode

    If wat_src is not provided, the module is extracted from the WAST file itself.

    Args:
        name: Test target name
        wast: WAST file with test assertions (may contain module definition)
        wat_src: Optional separate WAT source file (if module is in WAST, leave None)
        platform: Renode platform description file
        tags: Additional tags
        **kwargs: Additional arguments passed to renode_test
    """

    # Use WAST as source if no separate WAT provided (module embedded in WAST)
    src_file = wat_src if wat_src else wast

    # Generate multi-function ELF from WAT/WAST
    elf_name = name + "_elf"
    native.genrule(
        name = elf_name,
        srcs = [src_file],
        outs = [name + ".elf"],
        cmd = "$(location //crates:synth) compile $(location {}) -o $@ --cortex-m --all-exports".format(src_file),
        tools = ["//crates:synth"],
    )

    # Generate Robot test from WAST with ELF symbol table
    robot_name = name + "_robot"
    # Platform path needs to be relative from the test directory to the renode directory
    # e.g., //tests/renode:synth_cortex_m.repl -> ${CURDIR}/../renode/synth_cortex_m.repl
    if ":" in platform:
        pkg_path = platform.split("//")[-1].split(":")[0]  # e.g., "tests/renode"
        filename = platform.split(":")[-1]  # e.g., "synth_cortex_m.repl"
        platform_path = "\\$${CURDIR}/../" + pkg_path.split("/")[-1] + "/" + filename
    else:
        platform_path = platform

    native.genrule(
        name = robot_name,
        srcs = [wast, ":" + elf_name],
        outs = [name + "_test.robot"],
        cmd = "$(location //crates:synth-test) generate --wast $(location {}) --robot $@ --platform '{}' --elf $(location :{})".format(
            wast,
            platform_path,
            elf_name
        ),
        tools = ["//crates:synth-test"],
    )

    # Run Renode test
    renode_test(
        name = name,
        robot_test = ":" + robot_name,
        deps = [platform],  # Platform file is always needed
        variables_with_label = {
            "ELF": ":" + elf_name,
        },
        tags = tags + ["wast", "multi-func"],
        **kwargs
    )


def wast_test_suite(
    name,
    wast_files,
    wat_src,
    platform = "//tests/renode:synth_cortex_m.repl",
    tags = [],
    **kwargs):
    """
    Create multiple WAST tests from a list of WAST files.

    Args:
        name: Suite name prefix
        wast_files: List of WAST files
        wat_src: WAT source file to compile (shared across tests)
        platform: Renode platform description file
        tags: Additional tags
        **kwargs: Additional arguments passed to wast_test
    """
    tests = []
    for wast in wast_files:
        # Extract test name from file path
        test_name = wast.replace("/", "_").replace(".wast", "")
        wast_test(
            name = name + "_" + test_name,
            wast = wast,
            wat_src = wat_src,
            platform = platform,
            tags = tags,
            **kwargs
        )
        tests.append(name + "_" + test_name)

    # Create test suite target
    native.test_suite(
        name = name,
        tests = tests,
        tags = tags,
    )
