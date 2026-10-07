"""Run all exact Sage checks, including article subdirectories."""
from pathlib import Path
import os
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from project import cache_path

scripts = sorted(path for path in (ROOT / 'checks/sage').rglob('*')
                 if path.suffix in ('.sage', '.py'))
env = os.environ.copy()
env['DOT_SAGE'] = str(cache_path() / 'sage')
Path(env['DOT_SAGE']).mkdir(parents=True, exist_ok=True)
for script in scripts:
    print(script.relative_to(ROOT), flush=True)
    subprocess.run(['sage', '-python', str(script)], cwd=ROOT, env=env, check=True)
