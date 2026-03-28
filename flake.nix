{
  description = "Synth — WebAssembly-to-ARM Cortex-M AOT compiler";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        # Rust toolchain: stable, edition 2024, MSRV 1.88
        rustToolchain = pkgs.rust-bin.stable."1.88.0".default.override {
          extensions = [
            "rust-src"
            "rust-analyzer"
            "clippy"
            "rustfmt"
            "llvm-tools-preview"
          ];
          targets = [
            "thumbv7em-none-eabihf"  # Cortex-M4F / M7 with hardware FPU
            "thumbv7em-none-eabi"    # Cortex-M4 / M7 without hardware FPU
            "thumbv7m-none-eabi"     # Cortex-M3
          ];
        };

        # Rocq 9 / Coq for proof verification
        # nixpkgs-unstable provides coq 8.20 (= Rocq 9.0)
        coq =
          if builtins.hasAttr "coq_8_20" pkgs then pkgs.coq_8_20
          else pkgs.coq;

        # Common packages for all systems
        commonPackages = [
          # -- Rust ---------------------------------------------------
          rustToolchain
          pkgs.cargo-llvm-cov        # Code coverage
          pkgs.cargo-nextest         # Better test runner
          pkgs.cargo-watch           # Watch mode

          # -- ARM cross-compilation ----------------------------------
          pkgs.gcc-arm-embedded      # arm-none-eabi-gcc toolchain

          # -- Proof verification -------------------------------------
          coq                        # Rocq 9 / Coq 8.20

          # -- SMT solver ---------------------------------------------
          pkgs.z3                    # Z3 for translation validation

          # -- Build system -------------------------------------------
          pkgs.bazelisk              # Bazel launcher (respects .bazelversion)
          pkgs.bazel-buildtools      # buildifier, buildozer

          # -- General dev tools --------------------------------------
          pkgs.pkg-config
          pkgs.openssl
          pkgs.git
          pkgs.jq
          pkgs.wabt                  # WebAssembly Binary Toolkit (wasm2wat, wat2wasm)
        ];

        # Platform-specific packages
        darwinPackages = pkgs.lib.optionals pkgs.stdenv.hostPlatform.isDarwin (with pkgs; [
          darwin.apple_sdk.frameworks.Security
          darwin.apple_sdk.frameworks.SystemConfiguration
          libiconv
        ]);

        linuxPackages = pkgs.lib.optionals pkgs.stdenv.hostPlatform.isLinux [
          pkgs.renode               # Emulation testing (Linux only in nixpkgs)
        ];

      in
      {
        devShells.default = pkgs.mkShell {
          name = "synth-dev";

          buildInputs = commonPackages ++ darwinPackages ++ linuxPackages;

          shellHook = ''
            echo "synth dev shell"
            echo "  rust:    $(rustc --version)"
            echo "  cargo:   $(cargo --version)"
            echo "  z3:      $(z3 --version 2>&1 | head -1)"
            echo "  bazel:   $(bazelisk version 2>/dev/null | head -1 || echo 'available via bazelisk')"
            echo "  arm-gcc: $(arm-none-eabi-gcc --version 2>/dev/null | head -1 || echo 'available')"
            echo "  coq:     $(coqc --version 2>/dev/null | head -1 || echo 'available')"
            ${if pkgs.stdenv.hostPlatform.isLinux then ''
              echo "  renode:  $(renode --version 2>/dev/null | head -1 || echo 'available')"
            '' else ''
              echo "  renode:  use Bazel rules_renode (not packaged for macOS)"
            ''}
            echo ""
            echo "Quick start:"
            echo "  cargo test --workspace             # Run all tests"
            echo "  cargo clippy --workspace           # Lint"
            echo "  bazelisk test //coq:verify_proofs  # Verify Rocq proofs"
            echo "  bazelisk test //tests/...          # Renode emulation tests"
          '';

          # Ensure Cargo can find system libraries
          PKG_CONFIG_PATH = "${pkgs.openssl.dev}/lib/pkgconfig";

          # Z3 headers for synth-verify (z3-sys crate static linking)
          Z3_SYS_Z3_HEADER = "${pkgs.z3.dev}/include/z3.h";

          # libclang for bindgen (used by z3-sys and other -sys crates)
          LIBCLANG_PATH = "${pkgs.llvmPackages.libclang.lib}/lib";

          # Bazel needs a C compiler
          CC = "cc";
        };

        # Expose the Rust toolchain as a package for other flakes to consume
        packages.rust-toolchain = rustToolchain;
      }
    );
}
