"""MkDocs hook: links from the documentation to files of the repository.

The pages in docs/ link to the examples and sources with relative paths
(`../examples/Demo/draft.tex`), which work when the Markdown is read on GitHub.
On the site those files do not exist, so the links point to GitHub instead.
"""
import os
import posixpath
import re

REPO = "https://github.com/Corrram/proofread"
BRANCH = "main"
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LINK = re.compile(r"(\]\()(\.\./[^)\s#]+)(#[^)\s]*)?(\))")


def on_page_markdown(markdown, page, config, files):
    base = posixpath.dirname(page.file.src_uri)

    def repo_link(match):
        target = posixpath.normpath(posixpath.join("docs", base, match.group(2)))
        if target.startswith(".."):
            return match.group(0)
        kind = "tree" if os.path.isdir(os.path.join(ROOT, target)) else "blob"
        return f"{match.group(1)}{REPO}/{kind}/{BRANCH}/{target}{match.group(3) or ''}{match.group(4)}"

    return LINK.sub(repo_link, markdown)
