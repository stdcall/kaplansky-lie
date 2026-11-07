"""Run every exact computation of the book with SageMath."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
checks = sorted((root / 'checks/sage').glob('*.py'))
if not checks:
    raise SystemExit('At least one exact computation is required')
for check in checks:
    subprocess.run(['sage', '-python', str(check)], cwd=root, check=True)
