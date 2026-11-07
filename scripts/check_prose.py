"""Advisory Russian prose checks; Vale parses Typst through typst2vast."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    config = json.loads((ROOT / 'config/project.json').read_text())
    assert config['prose']['checker'] == 'vale'
    sources = sorted((ROOT / 'content').rglob('*.typ'))
    result = subprocess.run(
        ['vale', '--config', str(ROOT / 'config/vale/.vale.ini'),
         '--output', 'JSON', *map(str, sources)],
        capture_output=True, text=True)
    if result.stderr.strip() or 'typst2vast not found' in result.stdout:
        raise SystemExit(result.stderr + result.stdout)
    try:
        issues = json.loads(result.stdout)
    except json.JSONDecodeError:
        raise SystemExit(result.stdout or 'Vale returned no report')
    count = 0
    for name, findings in issues.items():
        for item in findings:
            count += 1
            print(f'{Path(name).relative_to(ROOT)}:{item["Line"]}:'
                  f'{item["Span"][0]}: {item["Check"]}: {item["Message"]}')
    print(f'Vale: {count} findings (advisory).')


if __name__ == '__main__':
    main()
