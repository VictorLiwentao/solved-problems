"""Build the alphabetical index, JSON catalogue and individual BibTeX downloads."""
import argparse
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPO = "https://github.com/VictorLiwentao/solved-problems"
RAW = "https://raw.githubusercontent.com/VictorLiwentao/solved-problems"
DRAFT_LINK = re.compile(r"\]\(((?:\.\./results/[\w-]+/)?[\w-]+/)(?:README\.md)?\)")
WEB_LINK = re.compile(r"\[([^\]]+)\]\((https?://[^)\s]+)\)")


def table_rows(index, width):
    rows = {}
    for line in index.read_text().splitlines():
        if not line.startswith("|"):
            continue
        cells = line.strip("|").strip().split(" | ")
        match = DRAFT_LINK.search(cells[0])
        if match is None:
            continue
        path = (index.parent / match[1]).resolve().relative_to(ROOT).as_posix()
        if len(cells) != width or path in rows:
            raise ValueError(f"Unexpected or duplicate catalogue row for {path} in {index}")
        rows[path] = cells
    return rows


def bib_field(entry, name):
    # The repository keeps each field on one line and wraps titles in extra braces.
    value = re.search(rf"^  {name} = \{{(.*)\}},?$", entry, flags=re.MULTILINE)
    if not value:
        raise ValueError(f"Missing {name} in {entry.splitlines()[0]}")
    return value[1].removeprefix("{").removesuffix("}") if name == "title" else value[1]


def build():
    folders = {str(p.parent.relative_to(ROOT)) for p in (ROOT / "results").glob("*/*/README.md")}
    summaries = {}
    for field_dir in sorted({(ROOT / folder).parent for folder in folders}):
        rows = table_rows(field_dir / "README.md", 3)
        if any((ROOT / path).parent != field_dir for path in rows):
            raise ValueError(f"Draft listed under the wrong field in {field_dir}")
        summaries.update(rows)
    sources = table_rows(ROOT / "docs/scores-and-sources.md", 5)
    bibliography = (ROOT / "citations.bib").read_text()
    entries = re.findall(r"^@unpublished\{.*?^\}\n", bibliography, flags=re.MULTILINE | re.DOTALL)
    if not (set(summaries) == set(sources) == folders) or len(entries) != len(folders):
        raise ValueError("The catalogue, source table, bibliography, and draft folders must agree")

    outputs = {}
    drafts = []
    index_rows = []
    for entry in entries:
        url = bib_field(entry, "url")
        pin = re.fullmatch(re.escape(REPO) + r"/tree/([0-9a-f]{40})/(results/[\w-]+/[\w-]+)", url)
        if not pin:
            raise ValueError(f"Expected a revision-pinned draft URL in {url}")
        revision, folder = pin.groups()
        _, field, slug = folder.split("/")
        bib_path = ROOT / folder / "citation.bib"
        if folder not in folders or bib_path in outputs:
            raise ValueError(f"Unknown or duplicate bibliography entry for {folder}")
        outputs[bib_path] = entry
        _, _, year, attribution, _ = sources[folder]
        links = WEB_LINK.findall(attribution)
        if not links:
            raise ValueError(f"Missing original source for {folder}")
        family, given = bib_field(entry, "author").split(", ", 1)
        raw_folder = f"{RAW}/{revision}/{folder}"
        for ext in ("pdf", "tex"):
            if not (ROOT / folder / f"{slug}.{ext}").is_file():
                raise ValueError(f"Missing {ext} for {folder}")
        title = bib_field(entry, "title")
        field_name = field.replace("-", " ").capitalize()
        relative_folder = f"{field}/{slug}"
        index_rows.append((
            title.casefold(),
            f"| [{title}]({relative_folder}/README.md) | [{field_name}]({field}/README.md) | "
            f"[PDF]({relative_folder}/{slug}.pdf) |",
        ))
        drafts.append({
            "citation_key": entry.split("{", 1)[1].split(",", 1)[0],
            "title": title,
            "author": f"{given} {family}",
            "year": int(bib_field(entry, "year")),
            "field": field_name,
            "proposed_result": summaries[folder][1],
            "status": "Research draft. Independent proof and priority review pending.",
            "original_question": {
                "source_year": int(year),
                "attribution": WEB_LINK.sub(r"\1", attribution),
                "references": [{"label": label, "url": link} for label, link in links],
            },
            "assistance": bib_field(entry, "note"),
            "draft_url": f"{REPO}/tree/main/{folder}",
            "cited_version": url,
            "pdf": f"{raw_folder}/{slug}.pdf",
            "latex": f"{raw_folder}/{slug}.tex",
            "bibtex": f"{RAW}/main/{folder}/citation.bib",
        })

    catalogue = {
        "title": "Mathematical research notes",
        "author": {"name": "Wentao Li", "profile": "https://github.com/VictorLiwentao"},
        "repository": REPO,
        "bibliography": f"{RAW}/main/citations.bib",
        "drafts": sorted(drafts, key=lambda d: (d["field"], d["title"].casefold())),
    }
    outputs[ROOT / "catalogue.json"] = json.dumps(catalogue, ensure_ascii=False, indent=2) + "\n"
    index = [
        "# All research drafts",
        "",
        "[Browse by field](../README.md#browse-the-collection) · [Original questions and scores](../docs/scores-and-sources.md) · [Lean proofs](../lean/README.md)",
        "",
        f"The {len(drafts)} drafts are listed alphabetically by manuscript title. Each title opens the result page with the original question, proof and citation.",
        "",
        "| Manuscript | Field | PDF |",
        "| --- | --- | --- |",
    ]
    index.extend(row for _, row in sorted(index_rows))
    outputs[ROOT / "results/README.md"] = "\n".join(index) + "\n"
    return outputs


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="report stale or missing exports")
    check = parser.parse_args().check
    stale = []
    for path, expected in build().items():
        if path.is_file() and path.read_text() == expected:
            continue
        if check:
            stale.append(str(path.relative_to(ROOT)))
        else:
            path.write_text(expected)
    if stale:
        raise SystemExit("Regenerate with python3 scripts/build_catalogue.py:\n" + "\n".join(stale))
