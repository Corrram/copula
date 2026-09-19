"""Validate the rendered handbook, its theorem anchors, and dependency pins."""

import argparse
from html.parser import HTMLParser
import json
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]


class Page(HTMLParser):
    def __init__(self, path):
        super().__init__(convert_charrefs=True)
        self.ids = set()
        self.links = []
        self.math = 0
        self.raw_math = []
        self.ignored_depth = 0
        self.feed(path.read_text(encoding="utf-8"))

    def handle_starttag(self, tag, attrs):
        if tag in {"script", "style", "pre", "code"}:
            self.ignored_depth += 1
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        if tag == "a" and "href" in attrs:
            self.links.append(attrs["href"])
        if "arithmatex" in attrs.get("class", "").split():
            self.math += 1

    def handle_endtag(self, tag):
        if tag in {"script", "style", "pre", "code"}:
            self.ignored_depth -= 1

    def handle_data(self, data):
        if not self.ignored_depth and "$$" in data:
            self.raw_math.append(data)


def validate(full):
    from docs_hook import THEOREMS, source_location

    assert (ROOT / "lean-toolchain").read_text().strip() == (ROOT / "docbuild/lean-toolchain").read_text().strip()
    manifests = [json.loads((ROOT / path).read_text()) for path in
                 ("lake-manifest.json", "docbuild/lake-manifest.json")]
    pins = [{p["name"]: p.get("rev") for p in m["packages"]} for m in manifests]
    for name, rev in pins[0].items():
        assert pins[1].get(name) == rev, f"Documentation dependency differs: {name}"
    for item in THEOREMS.values():
        source_location(item)

    site = ROOT / "site"
    cache = {}

    def read(path):
        if path not in cache:
            assert path.is_file(), f"Missing generated page: {path.relative_to(ROOT)}"
            cache[path] = Page(path)
        return cache[path]

    if full:
        landing = read(site / "api/Copula.html")
        assert "copula-api" in landing.ids, "Missing Copula API topic index"
        for href in landing.links:
            if href.startswith("Copula/"):
                assert (site / "api" / href).is_file(), f"Missing API topic: {href}"
        for item in THEOREMS.values():
            path = site / "api" / (item["module"].replace(".", "/") + ".html")
            assert item["declaration"] in read(path).ids, f"Missing formal declaration: {item['declaration']}"
        modules = [ROOT / "Copula.lean", *(ROOT / "Copula").rglob("*.lean")]
        for source in modules:
            assert (site / "api" / source.relative_to(ROOT).with_suffix(".html")).is_file(), f"Missing API module: {source}"
        for asset in ["index.html", "search.html", "search.js", "find/index.html", "declarations/declaration-data.bmp"]:
            assert (site / "api" / asset).stat().st_size > 0, f"Missing API search asset: {asset}"

    for path in site.rglob("*.html"):
        if "api" in path.relative_to(site).parts or path.name == "404.html":
            continue
        page = read(path)
        assert not page.raw_math, f"Unprocessed display mathematics in {path}: {page.raw_math}"
        if "handbook" in path.parts:
            assert page.math > 0, f"No rendered math containers: {path}"
        for href in page.links:
            link = urlsplit(href)
            if link.scheme or link.netloc or href.startswith("/"):
                continue
            target = (path.parent / unquote(link.path)).resolve() if link.path else path
            assert target.is_relative_to(site), f"Link escapes site: {path}: {href}"
            if not full and "api" in target.relative_to(site).parts:
                continue
            if target.is_dir():
                target /= "index.html"
            assert target.is_file(), f"Broken link in {path.relative_to(site)}: {href}"
            if target.suffix == ".html" and link.fragment:
                assert unquote(link.fragment) in read(target).ids, f"Missing anchor in {path.relative_to(site)}: {href}"
    print(f"Validated {len(THEOREMS)} formal references, dependency pins, and handbook links"
          + (", including generated API anchors and all Copula modules." if full else " (handbook-only preview)."))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--handbook-only", action="store_true")
    args = parser.parse_args()
    validate(not args.handbook_only)
