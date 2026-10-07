"""Advisory check of Russian prose with Vale and its Typst parser."""
from pathlib import Path
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    result = subprocess.run([
        'vale', '--config', str(ROOT / 'checks/vale/.vale.ini'),
        '--output', 'JSON',
        *map(str, sorted((ROOT / 'content').rglob('*.typ'))),
    ], capture_output=True, text=True)
    if result.returncode not in (0, 1):
        raise SystemExit(result.stdout + result.stderr)
    findings = json.loads(result.stdout or '{}')
    count = 0
    for path, items in findings.items():
        for item in items:
            count += 1
            print(f'{Path(path).relative_to(ROOT)}:{item["Line"]}: '
                  f'{item["Check"]}: {item["Message"]}')
    print(f'Vale: {count} findings (advisory)')


if __name__ == '__main__':
    main()
