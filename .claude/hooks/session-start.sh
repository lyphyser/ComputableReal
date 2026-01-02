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

# Install lean4-theorem-proving skill
echo "Installing lean4-theorem-proving skill..."
SKILLS_REPO="$HOME/lean4-skills"
if [ ! -d "$SKILLS_REPO" ]; then
  git clone https://github.com/cameronfreer/lean4-skills.git "$SKILLS_REPO"
fi
mkdir -p ~/.claude/skills
cp -r "$SKILLS_REPO/plugins/lean4-theorem-proving" ~/.claude/skills/
echo "Skill installation complete!"

# Add MCP servers from .claude/mcp.json to home directory config
echo "Configuring MCP servers..."
CLAUDE_CONFIG="$HOME/.claude.json"
PROJECT_PATH="/home/user/ComputableReal"
PROJECT_MCP_CONFIG="$PROJECT_PATH/.claude/mcp.json"

if [ -f "$CLAUDE_CONFIG" ] && [ -f "$PROJECT_MCP_CONFIG" ]; then
  if command -v jq &> /dev/null; then
    # Read MCP servers from project config and merge into root level mcpServers
    TMP_FILE=$(mktemp)
    jq --slurpfile mcp "$PROJECT_MCP_CONFIG" \
       '.mcpServers = ($mcp[0].mcpServers // {})' \
       "$CLAUDE_CONFIG" > "$TMP_FILE" && mv "$TMP_FILE" "$CLAUDE_CONFIG"
    echo "MCP servers configured from .claude/mcp.json"
  else
    echo "Warning: jq not found, skipping MCP server configuration"
  fi
else
  [ ! -f "$CLAUDE_CONFIG" ] && echo "Warning: Claude config not found at $CLAUDE_CONFIG"
  [ ! -f "$PROJECT_MCP_CONFIG" ] && echo "Warning: Project MCP config not found at $PROJECT_MCP_CONFIG"
fi
