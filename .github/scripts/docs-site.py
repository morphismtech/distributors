"""The documentation site, on the gh-pages branch.

    docs-site.py describe DOCS
        Record what the documentation in DOCS was built from, as DOCS/SITE.json:
        the commit, & each package's name & synopsis, from its .cabal file.

    docs-site.py index
        Write index.html at the root of the gh-pages checkout in the current
        directory, describing main's documentation, in main/, & each pull
        request's preview, in pr-preview/pr-<number>/, by their SITE.json.
        It removes the previews of closed pull requests, & those left empty,
        such as by a removal which leaves a .nojekyll behind.
"""

import datetime
import html
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import urllib.request

REPO = os.environ.get("GITHUB_REPOSITORY", "morphismtech/distributors")
OWNER, NAME = REPO.split("/")
SITE = f"https://{OWNER}.github.io/{NAME}"
GITHUB = f"https://github.com/{REPO}"


def describe(docs: pathlib.Path) -> None:
    packages = []
    for cabal in sorted(pathlib.Path(".").glob("**/*.cabal")):
        if any(part.startswith(("dist-newstyle", ".")) for part in cabal.parts[:-1]):
            continue
        text = cabal.read_text()
        name = re.search(r"^name:\s*(\S+)", text, re.M | re.I)
        synopsis = re.search(r"^synopsis:\s*(.+)$", text, re.M | re.I)
        if name and (docs / name.group(1)).is_dir():
            packages.append({
                "name": name.group(1),
                "synopsis": synopsis.group(1).strip() if synopsis else "",
            })
    site = {
        "commit": os.environ.get("GITHUB_SHA", ""),
        "built": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M UTC"),
        "packages": packages,
    }
    (docs / "SITE.json").write_text(json.dumps(site, indent=2) + "\n")


def pull_request(number: str) -> dict:
    headers = {"Accept": "application/vnd.github+json"}
    if os.environ.get("GITHUB_TOKEN"):
        headers["Authorization"] = f"Bearer {os.environ['GITHUB_TOKEN']}"
    request = urllib.request.Request(
        f"https://api.github.com/repos/{REPO}/pulls/{number}", headers=headers
    )
    try:
        with urllib.request.urlopen(request) as response:
            return json.load(response)
    except Exception:
        return {}


def site_of(path: pathlib.Path) -> dict:
    try:
        return json.loads((path / "SITE.json").read_text())
    except (OSError, ValueError):
        return {}


def packages_html(base: str, site: dict) -> str:
    if not site.get("packages"):
        return f'<a href="{base}/">Contents</a>'
    items = "".join(
        f'<li><a href="{base}/{html.escape(p["name"])}/"><code>{html.escape(p["name"])}</code></a>'
        + (f' &mdash; {html.escape(p["synopsis"])}' if p["synopsis"] else "")
        + "</li>"
        for p in site["packages"]
    )
    return f'<ul class="packages">{items}</ul><p><a href="{base}/">All modules &amp; the index</a></p>'


def commit_html(site: dict) -> str:
    commit = site.get("commit", "")
    if not commit:
        return ""
    return (
        f'Built from <a href="{GITHUB}/commit/{commit}"><code>{commit[:7]}</code></a>'
        f' on {html.escape(site.get("built", ""))}.'
    )


def index() -> None:
    root = pathlib.Path(".")
    main = site_of(root / "main")
    if (root / "main").is_dir():
        main_html = f"<p>{commit_html(main)}</p>{packages_html('main', main)}"
    else:
        main_html = "<p>Not published yet: it is published when <code>main</code> changes.</p>"

    previews = sorted(
        (p for p in (root / "pr-preview").glob("pr-*") if p.is_dir()),
        key=lambda p: int(p.name[3:]) if p.name[3:].isdigit() else 0,
        reverse=True,
    )
    rows = []
    for preview in previews:
        number = preview.name[3:]
        pr = pull_request(number)
        # A preview without documentation, or of a closed pull request, is
        # stale; one whose pull request is unknown is kept, unless empty.
        empty = not any(not p.name.startswith(".") for p in preview.iterdir())
        if empty or pr.get("state") == "closed":
            shutil.rmtree(preview)
            continue
        site = site_of(preview)
        title = html.escape(pr.get("title", ""))
        branch = html.escape(pr.get("head", {}).get("ref", ""))
        rows.append(
            "<tr>"
            f'<td><a href="{GITHUB}/pull/{number}">#{number}</a></td>'
            f"<td>{title}<br><code>{branch}</code></td>"
            f'<td>{packages_html(f"pr-preview/{preview.name}", site)}</td>'
            f"<td>{commit_html(site)}</td>"
            "</tr>"
        )
    if rows:
        previews_html = (
            "<table><thead><tr><th>Pull request</th><th>Title &amp; branch</th>"
            "<th>Documentation</th><th>Built</th></tr></thead><tbody>"
            + "".join(rows)
            + "</tbody></table>"
        )
    else:
        previews_html = "<p>No open pull request has a preview.</p>"

    page = f"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{NAME} documentation</title>
<style>
  :root {{ --fg: #1f2328; --bg: #ffffff; --muted: #59636e; --line: #d1d9e0; --link: #0969da; }}
  @media (prefers-color-scheme: dark) {{
    :root {{ --fg: #e6edf3; --bg: #0d1117; --muted: #9198a1; --line: #3d444d; --link: #4493f8; }}
  }}
  body {{ font: 16px/1.5 system-ui, sans-serif; color: var(--fg); background: var(--bg);
         max-width: 60rem; margin: 0 auto; padding: 2rem 1rem; }}
  a {{ color: var(--link); }}
  h1 {{ margin-bottom: 0; }}
  .lede, .muted, td:last-child {{ color: var(--muted); }}
  table {{ border-collapse: collapse; width: 100%; }}
  th, td {{ text-align: left; vertical-align: top; padding: .5rem; border-bottom: 1px solid var(--line); }}
  .packages {{ margin: .25rem 0; padding-left: 1.25rem; }}
  td .packages, td p {{ margin: 0; }}
  @media (max-width: 40rem) {{ th:last-child, td:last-child {{ display: none; }} }}
</style>
</head>
<body>
<h1>{NAME} documentation</h1>
<p class="lede">Haddock documentation for the <a href="{GITHUB}">{NAME}</a> packages,
built from <code>main</code> & from each open pull request.</p>

<h2><code>main</code></h2>
<p>The documentation of the latest development version, published whenever <code>main</code> changes.
Released versions are documented on <a href="https://hackage.haskell.org/package/{NAME}">Hackage</a>.</p>
{main_html}

<h2>Pull request previews</h2>
<p>The documentation of each open pull request from this repository, as it would be if merged,
updated whenever the pull request changes & removed when it closes.</p>
{previews_html}

<p class="muted">Published by the <a href="{GITHUB}/blob/main/.github/workflows/docs.yml">Docs workflow</a>
to the <a href="{GITHUB}/tree/gh-pages"><code>gh-pages</code></a> branch.</p>
</body>
</html>
"""
    (root / "index.html").write_text(page)
    (root / ".nojekyll").touch()


if __name__ == "__main__":
    if sys.argv[1:2] == ["describe"] and len(sys.argv) == 3:
        describe(pathlib.Path(sys.argv[2]))
    elif sys.argv[1:] == ["index"]:
        index()
    else:
        sys.exit(__doc__)
