FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04

# Only the manager and prerequisites are installed here. The pinned Lean
# toolchain, Mathlib cache, and proof build run only on the reader's command.
RUN apt-get update && apt-get install -y --no-install-recommends \
    elan python3 git curl ca-certificates build-essential zstd \
    && rm -rf /var/lib/apt/lists/*
