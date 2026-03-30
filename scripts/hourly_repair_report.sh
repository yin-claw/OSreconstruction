#!/bin/bash
set -euo pipefail

REPO="$HOME/.openclaw/workspace/OSreconstruction"
REPORT="$REPO/FALSE_THEOREM_INVESTIGATION_REPORT.md"
NOW_UTC=$(date -u '+%Y-%m-%d %H:%M UTC')
HEAD=$(git -C "$REPO" rev-parse --short HEAD)
BRANCH=$(git -C "$REPO" branch --show-current)
STATUS=$(git -C "$REPO" status --short | sed -n '1,40p')
LAST_COMMITS=$(git -C "$REPO" log --oneline -5)
DIFFSTAT=$(git -C "$REPO" diff --stat | sed -n '1,80p')
REPORT_HEAD=$(sed -n '1,120p' "$REPORT" 2>/dev/null || true)

python3 - <<'PY'
import json, os, subprocess, pathlib

repo = pathlib.Path(os.path.expanduser('~/.openclaw/workspace/OSreconstruction'))
now_utc = subprocess.check_output(['date', '-u', '+%Y-%m-%d %H:%M UTC'], text=True).strip()
head = subprocess.check_output(['git', '-C', str(repo), 'rev-parse', '--short', 'HEAD'], text=True).strip()
branch = subprocess.check_output(['git', '-C', str(repo), 'branch', '--show-current'], text=True).strip()
status = subprocess.check_output(['bash', '-lc', f'git -C {repo} status --short | sed -n "1,40p"'], text=True)
last_commits = subprocess.check_output(['git', '-C', str(repo), 'log', '--oneline', '-5'], text=True)
diffstat = subprocess.check_output(['bash', '-lc', f'git -C {repo} diff --stat | sed -n "1,80p"'], text=True)
report = (repo / 'FALSE_THEOREM_INVESTIGATION_REPORT.md').read_text() if (repo / 'FALSE_THEOREM_INVESTIGATION_REPORT.md').exists() else ''
report_head = '\n'.join(report.splitlines()[:120])

body = f"""Xi,

Automatic hourly status update for the OSreconstruction repair/investigation.

Timestamp
- {now_utc}

Repo state
- Repo: {repo}
- Branch: {branch}
- HEAD: {head}

Recent commits
{last_commits}

Current git status
{status}

Current diffstat
{diffstat}

Report excerpt
{report_head}

Notes
- This is the automatic hourly repair update.
- Current focus remains the false/over-strong theorem repair around exists_probeSeq_euclid_local, bvt_cluster, and the honest OS→Wightman export surface.

— Claw"""

payload = {
    'from': 'Claw <claw@seminairemath.com>',
    'to': ['xiyin137@gmail.com'],
    'subject': f'OSreconstruction repair status update — {now_utc}',
    'text': body,
}
with open('/tmp/osrepair_hourly_email.json', 'w') as f:
    json.dump(payload, f)
PY

curl -sS -X POST https://api.resend.com/emails \
  -H 'Authorization: Bearer re_FEdfvFir_KQ61Wuz8wdYjfgMWny5sjFVZ' \
  -H 'Content-Type: application/json' \
  --data-binary @/tmp/osrepair_hourly_email.json
