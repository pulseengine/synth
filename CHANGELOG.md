# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed
- Reorganized documentation structure - consolidated 41 root docs into organized `docs/` subdirectories
- Documentation now organized by category: status, sessions, analysis, planning, research, build-systems, validation, architecture

### Added
- GitHub project infrastructure: 40 labels, 4 milestones, 24 issues
- Project board for tracking reorganization progress

## [0.1.0] - TBD

### Planned
- Working CLI: `synth compile input.wasm -o output.elf`
- Calculator demo running on Zephyr/QEMU
- Complete CI/CD pipeline
- Comprehensive documentation

---

## Pre-release Development

### 2025-11-21
- Completed Phase 3a: 100% WASM Core 1.0 coverage (151 operations)
- Added Loom ASIL evaluation and integration analysis
- Added Bazel build system infrastructure

### 2025-11-17
- Initial codebase with 14 Rust crates
- Z3 verification framework
- ARM instruction encoding
- ELF generation
