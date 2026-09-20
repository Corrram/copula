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

topics = [
    ("Copula/Basic.html", "Copulas as probability measures"),
    ("Copula/CDF.html", "Distribution functions"),
    ("Copula/Sklar/General.html", "Sklar's theorem"),
    ("Copula/Families/FGM.html", "Families: start with FGM"),
    ("Copula/Rank/Basic.html", "Rank coefficients"),
    ("Copula/Dependence/Basic.html", "Positive dependence"),
    ("Copula/Order/Orthant.html", "Dependence orders"),
    ("Copula/OrdinalSum/Decomposition.html", "Ordinal sums and decomposition"),
    ("Copula/Vine/Regular.html", "C-, D-, and regular-vine copulas"),
]
overview = (
    '<section id="copula-api"><h1>Copula API</h1>'
    '<p>Browse the formal definitions and theorems by topic, or search for a '
    'declaration using the search box above. The module browser includes all '
    'Copula modules and their documented dependencies.</p><ul>'
    + "".join(f'<li><a href="{path}">{title}</a></li>' for path, title in topics)
    + '</ul><p>For mathematical notation and explanations, return to the '
    '<a href="../index.html">handbook</a>.</p></section>'
)
for path, _ in topics:
    assert (target / path).is_file(), f"Missing API topic: {path}"

# This small addition leaves doc-gen's own rendering and search intact.
for page in target.rglob("*.html"):
    depth = len(page.relative_to(target).parts) - 1
    handbook = "../" * (depth + 1) + "index.html"
    original = page.read_text(encoding="utf-8")
    content = original
    link = (f'<a class="copula-handbook-link" href="{handbook}" '
            'style="display:block;padding:.5rem 1rem;background:#075e56;color:white;'
            'font-family:system-ui,sans-serif;text-decoration:none">'
            '← Copula mathematical handbook</a>')
    if 'class="copula-handbook-link"' not in content:
        content = re.sub(r"(<main\b[^>]*>)", lambda match: match[0] + link, content, count=1)
    if page == target / "Copula.html" and 'id="copula-api"' not in content:
        assert link in content, "Copula API landing page has no main content area"
        content = content.replace(link, link + overview, 1)
    # Doc-gen's compact header otherwise has an unlabelled, empty search box.
    content = re.sub(
        r'<input\b(?=[^>]*\bname="q")[^>]*>',
        lambda match: match[0] if 'aria-label=' in match[0] else match[0].replace(
            'name="q"', 'name="q" aria-label="Search declarations" placeholder="Search declarations"'
        ),
        content,
    )
    if content != original:
        page.write_text(content, encoding="utf-8")
print(f"Assembled handbook and API in {ROOT / 'site'}")
