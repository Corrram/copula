"""Resolve handbook theorem references against the library's actual source files."""

import html
import json
import os
from pathlib import Path
import posixpath
import re
import subprocess
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[1]
THEOREMS = json.loads((ROOT / "docs/theorems.json").read_text(encoding="utf-8"))
REFERENCE = re.compile(r"(?m)(^[ \t]*)\{\{\s*lean:([a-z0-9-]+)\s*\}\}[ \t]*$")


def revision():
    return os.environ.get("DOCS_REVISION") or subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
    ).strip()


def source_location(item):
    source = ROOT / (item["module"].replace(".", "/") + ".lean")
    # A qualified theorem may be declared under a namespace or with a dotted name.
    pattern = re.compile(r"\b(?:theorem|def|structure|class|abbrev)\s+([\w'.]+)(?=[\s(:{])")
    matches = []
    for i, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
        match = pattern.search(line)
        if match and (item["declaration"] == match[1] or item["declaration"].endswith("." + match[1])):
            matches.append(i)
    if len(matches) != 1:
        raise ValueError(f"Expected one source declaration for {item['declaration']}, got {matches}")
    return source.relative_to(ROOT).as_posix(), matches[0]


def reference_html(key, page_url):
    item = THEOREMS[key]
    source, line = source_location(item)
    target = "api/" + item["module"].replace(".", "/") + ".html"
    directory = page_url if page_url.endswith("/") else posixpath.dirname(page_url)
    api = posixpath.relpath(target, directory or ".") + "#" + quote(item["declaration"])
    proof = f"https://github.com/Corrram/copula/blob/{revision()}/{source}#L{line}"
    return (f'<div class="lean-reference"><a href="{html.escape(api)}">Formal statement</a>'
            f'<a href="{proof}">Source and proof</a>'
            f'<code>{html.escape(item["declaration"])}</code></div>')


def on_page_markdown(markdown, page, config, files):
    if "<!-- theorem-index -->" in markdown:
        entries = []
        for key, item in THEOREMS.items():
            entries.append(f"### {item['title']}\n\n{{{{ lean:{key} }}}}\n")
        markdown = markdown.replace("<!-- theorem-index -->", "\n".join(entries))
    markdown = REFERENCE.sub(lambda m: m[1] + reference_html(m[2], page.url), markdown)
    # Existing coverage guides also link to repository files outside docs/.
    def repository_link(match):
        label, target = match.groups()
        path, _, fragment = target.partition("#")
        source = (Path(config.docs_dir) / page.file.src_path).parent / path
        source = source.resolve()
        if source.is_file() and source.is_relative_to(ROOT) and not source.is_relative_to(Path(config.docs_dir)):
            url = f"https://github.com/Corrram/copula/blob/{revision()}/{source.relative_to(ROOT).as_posix()}"
            return f"[{label}]({url}{'#' + fragment if fragment else ''})"
        return match[0]
    markdown = re.sub(r"\[([^\]]+)\]\((\.\./[^)]+)\)", repository_link, markdown)
    return markdown


def on_post_page(output, page, config):
    # Expose the exact source revision without implying the prose itself is machine checked.
    return output.replace("</article>",
        f'<p class="docs-revision">Library revision: <a href="https://github.com/Corrram/copula/tree/{revision()}">'
        f'<code>{revision()[:8]}</code></a> · Lean 4.34.0</p></article>')
