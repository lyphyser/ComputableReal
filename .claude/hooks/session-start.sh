#!/bin/bash
set -euo pipefail

# Only run in Claude Code on the web
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

echo "Setting up Lean environment..."

# Install elan if not already installed
if ! command -v elan &> /dev/null; then
  echo "Installing elan (Lean version manager)..."
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
fi

# Add elan to PATH for this session
echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$CLAUDE_ENV_FILE"
export PATH="$HOME/.elan/bin:$PATH"

# Ensure we're using the correct Lean version
elan show

# Download mathlib cache to avoid compiling dependencies from scratch
echo "Downloading mathlib cache..."
if ! lake exe cache get 2>&1 | grep -q "Completed successfully"; then
  echo "Warning: Cache download may have issues, but continuing..."
fi

echo "Lean environment setup complete!"
