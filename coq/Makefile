# Makefile for Synth Coq Verification
#
# This Makefile builds the Coq formalization of Synth's WebAssembly-to-ARM
# compilation and correctness proofs.

.PHONY: all clean validate theories install-deps

# Default target
all: theories

# Generate Makefile.coq from _CoqProject
Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

# Build all Coq theories
theories: Makefile.coq
	$(MAKE) -f Makefile.coq

# Validate all proofs (check for Admitted)
validate: theories
	@echo "Checking for admitted proofs..."
	@if grep -r "Admitted" theories/; then \
		echo "ERROR: Found admitted proofs"; \
		exit 1; \
	else \
		echo "SUCCESS: All proofs complete"; \
	fi

# Clean build artifacts
clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	find theories -name "*.vo" -delete
	find theories -name "*.vok" -delete
	find theories -name "*.vos" -delete
	find theories -name "*.glob" -delete
	find theories -name ".*.aux" -delete

# Install Coq dependencies
install-deps:
	@echo "Installing Coq and required libraries..."
	@echo "This requires opam to be installed."
	opam install -y coq.8.18.0
	opam install -y coq-mathcomp-ssreflect
	opam install -y coq-ext-lib
	opam install -y coq-stdpp

# Help
help:
	@echo "Synth Coq Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all          - Build all Coq theories (default)"
	@echo "  theories     - Build all Coq theories"
	@echo "  validate     - Check that no proofs are admitted"
	@echo "  clean        - Remove build artifacts"
	@echo "  install-deps - Install Coq and dependencies via opam"
	@echo "  help         - Show this help message"
