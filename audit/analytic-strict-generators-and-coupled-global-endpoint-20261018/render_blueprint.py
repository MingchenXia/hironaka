"""Render every full blueprint input in three foreground LaTeX passes."""
from pathlib import Path
import subprocess,shutil
A=Path(__file__).resolve().parent;ROOT=A.parents[1]
out=A/'blueprint-pdf-build';out.mkdir(exist_ok=True)
for number in range(1,4):
 with (A/f'blueprint-pass-{number}.stdout.log').open('w') as stream:
  subprocess.run(['pdflatex','-interaction=nonstopmode','-halt-on-error',
   '-output-directory',str(out),'extensions.tex'],cwd=ROOT/'blueprint',
   stdout=stream,stderr=subprocess.STDOUT,check=True)
 shutil.copyfile(out/'extensions.log',A/f'blueprint-pass-{number}.log')
 print('LATEX_PASS',number,'COMPLETE',flush=True)
