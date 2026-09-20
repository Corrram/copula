"""Refresh rendered doc-gen4 output while retaining reusable dependency analysis."""

from pathlib import Path
import json
import shutil

ROOT = Path(__file__).resolve().parents[1]


def prepare(root: Path = ROOT) -> None:
    root = root.resolve()
    modules = {"Copula"} | {
        ".".join(path.relative_to(root).with_suffix("").parts)
        for path in (root / "Copula").rglob("*.lean")
    }
    build = (root / "docbuild/.lake/build").resolve()
    html = (build / "doc").resolve()
    data = (build / "doc-data").resolve()
    if not build.is_relative_to(root) or html.parent != build or data.parent != build:
        raise ValueError("Refusing to clear documentation outside the project build directory")
    old_index = html / "declarations/declaration-data.bmp"
    if old_index.exists():
        old_modules = json.loads(old_index.read_text(encoding="utf-8"))["modules"]
        removed = {
            name for name in old_modules
            if (name == "Copula" or name.startswith("Copula.")) and name not in modules
        }
        if removed:
            # Retired modules must also leave the database's global tactic index.
            if data.exists():
                shutil.rmtree(data)
            for suffix in ("", "-shm", "-wal"):
                (build / f"api-docs.db{suffix}").unlink(missing_ok=True)
    if html.exists():
        shutil.rmtree(html)
    if data.exists():
        # Empty analysis markers can leave the HTML target looking up to date
        # even when a new imported module has been added to the database.
        for pattern in ("*.docs_built", "declaration-data-*.bmp", "backrefs-*.json",
                        "header-data.bmp", "references.json"):
            for rendered in data.glob(pattern):
                rendered.unlink()
        # The source revision is not tracked as an analysis dependency.
        for module in modules:
            (data / f"{module}.doc").unlink(missing_ok=True)


if __name__ == "__main__":
    prepare()
