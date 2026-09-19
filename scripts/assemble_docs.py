"""Copy the generated Lean API alongside the handbook; add a way back."""

from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
source = ROOT / "docbuild/.lake/build/doc"
target = ROOT / "site/api"
if not (source / "Copula.html").is_file():
    raise SystemExit("Missing generated API: run lake build Copula:docs in docbuild/ first")
if not (ROOT / "site/index.html").is_file():
    raise SystemExit("Missing handbook: run python -m mkdocs build --strict first")
shutil.copytree(source, target, dirs_exist_ok=True)
(ROOT / "site/.nojekyll").touch()

# This small addition leaves doc-gen's own rendering and search intact.
for page in target.rglob("*.html"):
    depth = len(page.relative_to(target).parts) - 1
    handbook = "../" * (depth + 1) + "index.html"
    content = page.read_text(encoding="utf-8")
    link = (f'<a class="copula-handbook-link" href="{handbook}" '
            'style="display:block;padding:.5rem 1rem;background:#075e56;color:white;'
            'font-family:system-ui,sans-serif;text-decoration:none">'
            '← Copula mathematical handbook</a>')
    if 'class="copula-handbook-link"' not in content:
        content = re.sub(r"(<main\b[^>]*>)", lambda match: match[0] + link, content, count=1)
        page.write_text(content, encoding="utf-8")
print(f"Assembled handbook and API in {ROOT / 'site'}")
