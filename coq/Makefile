# Makefile for Synth Rocq Verification
#
# This Makefile builds the Rocq (formerly Coq) formalization of Synth's
# WebAssembly-to-ARM compilation and correctness proofs.
#
# Compatible with: Rocq 9.0+, Coq 8.20+

.PHONY: all clean validate theories install-deps check-version

# Detect whether rocq or coqc is available
ROCQ := $(shell command -v rocq 2>/dev/null)
COQC := $(shell command -v coqc 2>/dev/null)

ifdef ROCQ
  COQ_MAKEFILE := rocq makefile
  COQ_CHECK := rocq check
  VERSION_CMD := rocq --version
else ifdef COQC
  COQ_MAKEFILE := coq_makefile
  COQ_CHECK := coqchk
  VERSION_CMD := coqc --version
else
  $(error "Neither rocq nor coqc found. Install via: opam install rocq-prover.9.0.0")
endif

# Default target
all: theories

# Show detected version
check-version:
	@echo "Detected proof assistant:"
	@$(VERSION_CMD)

# Generate Makefile.coq from _CoqProject
Makefile.coq: _CoqProject
	$(COQ_MAKEFILE) -f _CoqProject -o Makefile.coq

# Build all theories
theories: Makefile.coq
	$(MAKE) -f Makefile.coq

# Validate all proofs (check for Admitted)
validate: theories
	@echo "Checking for admitted proofs..."
	@admitted=$$(grep -r "Admitted" theories/ --include="*.v" | grep -v '^\s*(\*' || true); \
	if [ -n "$$admitted" ]; then \
		echo "WARNING: Found admitted proofs:"; \
		echo "$$admitted"; \
	else \
		echo "SUCCESS: All proofs complete (no Admitted)"; \
	fi

# Clean build artifacts
clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	find theories -name "*.vo" -delete 2>/dev/null || true
	find theories -name "*.vok" -delete 2>/dev/null || true
	find theories -name "*.vos" -delete 2>/dev/null || true
	find theories -name "*.glob" -delete 2>/dev/null || true
	find theories -name ".*.aux" -delete 2>/dev/null || true

# Install Rocq 9 and dependencies via opam
install-deps:
	@echo "Installing Rocq 9 and required libraries..."
	@echo "This requires opam to be installed."
	@command -v opam >/dev/null 2>&1 || { echo "opam not found. Install via: brew install opam"; exit 1; }
	opam install -y rocq-prover.9.0.0
	@echo ""
	@echo "Rocq 9 installed. Run 'make' to build proofs."

# Help
help:
	@echo "Synth Rocq Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all           - Build all theories (default)"
	@echo "  theories      - Build all theories"
	@echo "  validate      - Check that no proofs are admitted"
	@echo "  clean         - Remove build artifacts"
	@echo "  check-version - Show detected Rocq/Coq version"
	@echo "  install-deps  - Install Rocq 9 via opam"
	@echo "  help          - Show this help message"
