"""Regression checks for cached API pages after adding or removing a module."""

from pathlib import Path
import json
import tempfile
import unittest

from prepare_docs import prepare


class DocumentationCacheTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "Copula").mkdir()
        (self.root / "Copula/Basic.lean").write_text("")
        self.build = self.root / "docbuild/.lake/build"
        self.data = self.build / "doc-data"
        self.data.mkdir(parents=True)
        self.html = self.build / "doc"
        (self.html / "declarations").mkdir(parents=True)
        self.index(["Copula", "Copula.Basic", "Mathlib.Basic"])
        for marker in ("Copula--library.docs_built", "Copula.Basic.doc", "Mathlib.Basic.doc",
                       "declaration-data-Copula.bmp", "references.json"):
            (self.data / marker).write_text("")
        (self.build / "api-docs.db").write_text("cached database")

    def index(self, modules):
        (self.html / "declarations/declaration-data.bmp").write_text(
            json.dumps({"modules": {name: {} for name in modules}}))

    def test_new_module_forces_render_and_preserves_dependency_analysis(self):
        (self.root / "Copula/New.lean").write_text("")
        prepare(self.root)
        self.assertFalse(self.html.exists())
        self.assertEqual({p.name for p in self.data.iterdir()}, {"Mathlib.Basic.doc"})
        self.assertTrue((self.build / "api-docs.db").exists())
        prepare(self.root)

    def test_removed_module_clears_database(self):
        self.index(["Copula", "Copula.Basic", "Copula.Removed"])
        prepare(self.root)
        self.assertFalse(self.data.exists())
        self.assertFalse((self.build / "api-docs.db").exists())


if __name__ == "__main__":
    unittest.main()
