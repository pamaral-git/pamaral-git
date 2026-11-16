#!/usr/bin/env python3
"""
Markdown to Editorial CV PDF Generator
--------------------------------------
Converts markdown resume/CV files into high-end, ready-to-send PDF CV documents.
Styled after architectural, European editorial CV templates with grid lines,
two-column layout, and customizable color themes (Warm Linen, Dark Modern, Clean Minimal).

Usage:
    python3 md_to_cv_pdf.py input.md [output.pdf] [--photo photo.jpg] [--theme warm|dark|clean]
                            [--skills auto|bar|sidebar] [--min-zoom 0.86] [--engine auto|selenium|chrome]
                            [--lang en,pt-PT] [--translator auto|deepl|llm|argos] [--retranslate]

Portuguese (Portugal) version:
    python3 md_to_cv_pdf.py c-tech.md --lang pt-PT          -> c-tech.pt-PT.md + c-tech.pt-PT.pdf
    python3 md_to_cv_pdf.py c-tech.md --lang en,pt-PT       -> both PDFs in one run
  The English markdown is translated once and saved as <name>.pt-PT.md. That file is what gets
  rendered, so proofread and edit it freely; later runs reuse it (use --retranslate to redo it).
  Translation engines (--translator auto tries them in this order):
    deepl  DeepL API, target PT-PT.   Set DEEPL_API_KEY (the free API plan works).
    llm    Any OpenAI-compatible local server (llama-server, llama-swap, Ollama, LM Studio...),
           free and private. Set LLM_BASE_URL (default http://localhost:8080/v1) and LLM_MODEL.
    argos  Offline Argos Translate (pip install argostranslate); generic Portuguese, needs proofreading.

Requirements:
    Chrome/Chromium. Selenium is used when available; if Selenium cannot start
    (e.g. no matching chromedriver, offline), the script falls back to calling
    Chrome directly (--engine chrome), which needs no extra packages.

Markdown format understood (see c-tech.md / c-media.md):

    # Name
    **Tagline** ◦ Location ◦ email ◦ [github.com/user](https://github.com/user)   <- optional header line

    Bio paragraph(s).

    **Skills:**
    - Category: text            (a "Languages" category goes to its own block)

    ## Experience               (also: Timeline)
    - **[Org](url)** (2021–25) – Role
      - detail bullet
    ## Education
    - **Degree**, Institution (2023–2027). Notes.
    ## Selected builds          (also: Builds, Projects)
    ### [Name](url) ◦ Tagline ◦ [Repo](url)     <- featured build with bullets
    - bullet
    - **[Name](url)** ◦ one-line description    <- compact build card
    ## Hackathons / Other projects / Selected writing and media

Sections are rendered in the order they appear in the markdown (right column);
bio, education, languages (and skills in sidebar mode) go in the left column.
The layout fits one page when it can (switching skills to the sidebar and/or
shrinking slightly) and otherwise flows onto a second page.
"""

import argparse
import base64
import html as htmllib
import mimetypes
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
import json
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter


THEMES = {
    "warm": {
        "bg": "#F8F4ED",
        "text": "#0a0a0a",
        "text_muted": "#262626",
        "line": "#0a0a0a",
        "card_bg": "rgba(0, 0, 0, 0.025)",
        "card_border": "rgba(0, 0, 0, 0.16)",
        "photo_bg": "#eae4d8",
    },
    "dark": {
        "bg": "#121212",
        "text": "#F3F3F3",
        "text_muted": "#CCCCCC",
        "line": "#333333",
        "card_bg": "rgba(255, 255, 255, 0.04)",
        "card_border": "rgba(255, 255, 255, 0.18)",
        "photo_bg": "#1e1e1e",
    },
    "clean": {
        "bg": "#FFFFFF",
        "text": "#111111",
        "text_muted": "#333333",
        "line": "#222222",
        "card_bg": "#F9F9F9",
        "card_border": "#E0E0E0",
        "photo_bg": "#F0F0F0",
    },
}

DEFAULT_TAGLINE = "Philosophy & Technology ◦ Self-Hosted Systems, LLMs & Leadership"

# Used for any header field the markdown does not provide.
DEFAULT_CONTACT = {
    "location": "Braga, Portugal",
    "email": "pedromanuelamaral@gmail.com",
    "phone": "---/---",
    "github": "https://github.com/pamaral-git",
}

SECTION_TITLES = {
    "bio": "Profile & Vision",
    "skills_bar": "Core Competencies & Technical Skills",
    "skills_side": "Core Skills",
    "languages": "Languages",
    "education": "Education",
    "experience": "Experience & Leadership",
    "builds": "Selected Builds & AI Systems",
    "other_projects": "Other Projects",
    "hackathons": "Hackathons",
    "writing": "Selected Writing & Media",
}

SEP = "◦"

# --------------------------------------------------------------------------- #
# Inline markdown -> HTML
# --------------------------------------------------------------------------- #

def _esc(text: str) -> str:
    return htmllib.escape(text, quote=False)


def _emphasis(text: str) -> str:
    text = _esc(text)
    text = re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", text)
    text = re.sub(r"(?<![\*\w])\*(?!\s)(.+?)(?<!\s)\*(?![\*\w])", r"<em>\1</em>", text)
    return text


def format_markdown_inline(text: str) -> str:
    """Converts inline markdown (links, bold, italic, code) into safe HTML.

    Links and code are lifted out first so that characters inside URLs can never
    be mistaken for emphasis, and link labels may themselves contain emphasis.
    """
    if not text:
        return ""
    holders = []

    def hold(markup: str) -> str:
        holders.append(markup)
        return f"\x00{len(holders) - 1}\x00"

    text = re.sub(
        r"`([^`]+)`",
        lambda m: hold(f"<code>{_esc(m.group(1))}</code>"),
        text,
    )

    def link(m):
        label, url = m.group(1), m.group(2).strip().replace('"', "%22")
        return hold(
            f'<a href="{htmllib.escape(url, quote=False)}" target="_blank">{_emphasis(label)}</a>'
        )

    text = re.sub(r"\[([^\]]+)\]\(([^)\s]+)\)", link, text)
    text = _emphasis(text)
    return re.sub(r"\x00(\d+)\x00", lambda m: holders[int(m.group(1))], text)


# --------------------------------------------------------------------------- #
# Markdown parsing
# --------------------------------------------------------------------------- #

BULLET_RE = re.compile(r"^(\s*)[-*+]\s+(.*)$")
LINK_ONLY_RE = re.compile(r"^\[([^\]]+)\]\(([^)\s]+)\)$")
DATE_RE = re.compile(r"\(([^()]*(?:\d{4}|\bAY\b)[^()]*)\)")
EDU_TITLE_RE = re.compile(
    r"secondary school|undergraduate|bachelor|licenciatura|\bBA\b|\bBSc\b|\bMSc\b|"
    r"master|phd|degree|universit|"
    r"escola secund|secundári|mestrado|doutoramento|faculdade|bacharelato",
    re.I,
)


def classify_heading(text: str) -> str:
    h = text.lower()
    if ("other" in h and "project" in h) or ("outros" in h and "projet" in h):
        return "other_projects"
    if "hackathon" in h:
        return "hackathons"
    if "education" in h or "formação" in h or "educação" in h:
        return "education"
    if "skill" in h or "competenc" in h or "competência" in h:
        return "skills"
    if "writing" in h or "escrita" in h or ("media" in h and "selected" in h):
        return "writing"
    if "build" in h or "project" in h or "projet" in h:
        return "builds"
    if any(k in h for k in ("experience", "timeline", "employment", "leadership", "experiência")):
        return "experience"
    return "generic"


def is_section_heading(text: str) -> bool:
    """An ### heading that is really a top-level section (old c.md: '### Builds')."""
    if "[" in text or SEP in text or len(text.split()) > 4:
        return False
    return classify_heading(text) != "generic"


def parse_block(lines):
    """Splits lines into plain paragraphs and a tree of bullet items by indentation."""
    paras, items, stack, cur = [], [], [], []
    last_item = None

    def flush():
        nonlocal cur
        if cur:
            paras.append(" ".join(cur))
            cur = []

    for raw in lines:
        line = raw.expandtabs(4).rstrip()
        if not line.strip():
            flush()
            last_item = None
            continue
        m = BULLET_RE.match(line)
        if m:
            flush()
            indent = len(m.group(1))
            item = {"text": m.group(2).strip(), "children": []}
            while stack and stack[-1][0] >= indent:
                stack.pop()
            (stack[-1][1]["children"] if stack else items).append(item)
            stack.append((indent, item))
            last_item = item
        elif last_item is not None and line[0] in " \t":
            last_item["text"] += " " + line.strip()
        else:
            stack, last_item = [], None
            cur.append(line.strip())
    flush()
    return paras, items


def flat_children(item):
    out = []
    for c in item["children"]:
        out.append(c["text"])
        out.extend(flat_children(c))
    return out


def split_head(text: str):
    """'**[Title](url)** rest' / '[Title](url) rest' / 'Title' -> (title, url, rest)."""
    text = re.sub(r"^[^\w\*\[\(]+\s*", "", text.strip())  # leading emoji / symbols
    m = re.match(r"^\*\*(.+?)\*\*(.*)$", text, re.S)
    if m:
        head, rest = m.group(1).strip(), m.group(2)
    else:
        lm = re.match(r"^(\[[^\]]+\]\([^)]+\))(.*)$", text, re.S)
        head, rest = (lm.group(1), lm.group(2)) if lm else (text, "")
    lm = re.match(r"^\[(.+)\]\(([^)\s]+)\)$", head)
    if lm:
        return lm.group(1).strip(), lm.group(2).strip(), rest
    return head, "", rest


def tidy(text: str) -> str:
    text = re.sub(r"\s{2,}", " ", text)
    text = re.sub(r"\s+([.,;:])", r"\1", text)
    return re.sub(r"^[\s,;:\-–—]+", "", text).strip()


def split_entry(text: str):
    """'**Title** (dates) – rest'  ->  title, url, dates, rest."""
    title, url, rest = split_head(text)
    dates = ""
    dm = DATE_RE.search(title)  # old style: **Title (2019-2022)**
    if dm:
        dates = dm.group(1).strip()
        title = tidy(title[: dm.start()] + title[dm.end():])
    else:
        dm = DATE_RE.search(rest)
        if dm and dm.start() <= 60:
            dates = dm.group(1).strip()
            rest = rest[: dm.start()] + rest[dm.end():]
    return title, url, dates, tidy(rest)


def split_first_sentence(text: str):
    m = re.search(r"(?<=[A-Za-z0-9\)])\.\s+(?=[A-ZÀ-Ý])", text)
    if m:
        return text[: m.start()].strip(" ."), text[m.end():].strip()
    return text.strip(" ."), ""


def parse_name_desc(chunk: str):
    """'**[Name](url)** ◦ desc' / '[Name](url) (desc)' -> (name, url, desc)."""
    title, url, rest = split_head(chunk)
    rest = rest.strip()
    pm = re.match(r"^\((.+)\)$", rest)
    if pm:
        rest = pm.group(1)
    rest = re.sub(rf"^[{SEP}\-–—|:]\s*", "", rest).strip()
    return title, url, rest


def parse_skills(items):
    out = []
    for it in items:
        m = re.match(r"^\**\s*([^:*]+?)\s*\**\s*:\s*(.*)$", it["text"])
        if m:
            out.append((m.group(1).strip(), m.group(2).strip()))
    return out


def parse_build_from_heading(sub):
    parts = [p.strip() for p in sub["heading"].split(SEP)]
    name, url, _ = split_head(parts[0])
    tagline, extras = "", []
    for p in parts[1:]:
        lm = LINK_ONLY_RE.match(p)
        if lm:
            extras.append((lm.group(1), lm.group(2)))
        elif not tagline:
            tagline = p
    paras, items = parse_block(sub["lines"])
    bullets = [i["text"] for i in items] + paras
    return {"title": name, "url": url, "tagline": tagline, "extras": extras, "bullets": bullets}


def chunks_from_text(text: str):
    """Splits '**A** ◦ x ◦ **B** ◦ y' into ['**A** ◦ x', '**B** ◦ y']."""
    return [c.strip() for c in re.split(rf"\s+{SEP}\s+(?=\*\*)", text) if c.strip()]


def parse_builds(sec):
    builds, hackathons = [], ""
    for sub in sec["subs"]:
        builds.append(parse_build_from_heading(sub))
    texts = []
    for it in sec["items"]:
        texts.append((it["text"], flat_children(it)))
    for p in sec["paras"]:
        texts.append((p, []))
    for text, kids in texts:
        for chunk in chunks_from_text(text):
            title, url, desc = parse_name_desc(chunk)
            if title.lower().startswith("hackathon"):
                hackathons = desc
                continue
            builds.append({"title": title, "url": url, "tagline": desc, "extras": [], "bullets": kids})
    return builds, hackathons


def parse_other_projects(sec):
    texts = [i["text"] for i in sec["items"]] + sec["paras"]
    builds = []
    for text in texts:
        for part in re.split(rf"\s+{SEP}\s+", text):
            if not part.strip():
                continue
            title, url, desc = parse_name_desc(part)
            builds.append({"title": title, "url": url, "tagline": desc, "extras": [], "bullets": []})
    return builds


def parse_markdown_cv(md_text: str) -> dict:
    """Parses a markdown CV into structured components."""
    data = {
        "name": "Full Name",
        "tagline": DEFAULT_TAGLINE,
        "contact": {},
        "bio": [],
        "skills": [],
        "languages": [],
        "education": [],
        "sections": [],  # right-column blocks, in markdown order
    }

    def new_section(heading):
        return {"heading": heading, "kind": classify_heading(heading),
                "lines": [], "subs": []}

    name, intro, raw_sections, cur = None, [], [], None
    for raw in md_text.splitlines():
        line = raw.rstrip()
        if name is None and re.match(r"^#\s+\S", line):
            name = line[1:].strip()
            continue
        h2 = re.match(r"^##\s+(.*\S)\s*$", line)
        h3 = re.match(r"^###\s+(.*\S)\s*$", line)
        if h2:
            cur = new_section(h2.group(1))
            raw_sections.append(cur)
        elif h3:
            if is_section_heading(h3.group(1)) or cur is None:
                cur = new_section(h3.group(1))
                raw_sections.append(cur)
            else:
                cur["subs"].append({"heading": h3.group(1), "lines": []})
        elif line.strip() == "---":
            continue
        elif cur is None:
            intro.append(line)
        elif cur["subs"]:
            cur["subs"][-1]["lines"].append(line)
        else:
            cur["lines"].append(line)

    if name:
        data["name"] = name

    # ---- header line: **Tagline** ◦ place ◦ email ◦ [github](url)
    for i, line in enumerate(intro):
        if line.strip():
            if SEP in line and ("@" in line or "http" in line):
                parse_header_line(line, data)
                intro.pop(i)
            break

    # ---- intro: bio paragraphs + inline skills
    paras, items = parse_block(intro)
    data["bio"] = [p for p in paras
                   if not re.match(r"^\**(skills|compet[eê]ncias):?\**:?$", p.strip(), re.I)]
    skills = parse_skills(items)

    # ---- sections
    education, trailing_link = [], re.compile(r"curriculum|full cv|more about me", re.I)
    for sec in raw_sections:
        sec["paras"], sec["items"] = parse_block(sec["lines"])
    if raw_sections:  # drop a trailing "Full curriculum" link line
        last = raw_sections[-1]
        if last["paras"] and trailing_link.search(last["paras"][-1]) and "](" in last["paras"][-1]:
            last["paras"].pop()
        elif not last["paras"] and not last["items"] and not last["subs"]:
            raw_sections.pop()

    for sec in raw_sections:
        kind = sec["kind"]
        if kind == "skills":
            skills += parse_skills(sec["items"])
        elif kind == "education":
            for it in sec["items"]:
                education.append(make_education(it))
        elif kind == "experience":
            entries = []
            for it in sec["items"]:
                title, url, dates, rest = split_entry(it["text"])
                entry = {"title": title, "url": url, "dates": dates, "sub": rest,
                         "bullets": flat_children(it)}
                if EDU_TITLE_RE.search(title):
                    education.append(make_education(it))
                else:
                    entries.append(entry)
            data["sections"].append({"kind": "experience", "entries": entries})
        elif kind == "builds":
            builds, hackathons = parse_builds(sec)
            data["sections"].append({"kind": "builds", "builds": builds, "hackathons": hackathons})
        elif kind == "other_projects":
            data["sections"].append({"kind": "other_projects", "builds": parse_other_projects(sec)})
        elif kind == "hackathons":
            texts = [i["text"] for i in sec["items"]] + sec["paras"]
            body = f" {SEP} ".join(re.sub(r"^\*\*hackathons:?\*\*:?\s*", "", t, flags=re.I) for t in texts)
            data["sections"].append({"kind": "hackathons", "text": body})
        elif kind == "writing":
            texts = [i["text"] for i in sec["items"]] + sec["paras"]
            lines = [p.strip() for t in texts for p in re.split(rf"\s+{SEP}\s+", t) if p.strip()]
            data["sections"].append({"kind": "writing", "lines": lines})
        else:
            texts = [i["text"] for i in sec["items"]] + sec["paras"]
            data["sections"].append({"kind": "generic", "heading": sec["heading"], "lines": texts})

    for cat, val in skills:
        if cat.lower() in ("languages", "idiomas", "línguas"):
            data["languages"].append(val)
        else:
            data["skills"].append((cat, val))
    data["education"] = education
    return data


def make_education(item):
    title, url, dates, rest = split_entry(item["text"])
    inst, desc = split_first_sentence(rest) if rest else ("", "")
    extra = flat_children(item)
    if extra:
        desc = (desc + " " + " ".join(extra)).strip()
    return {"title": title, "url": url, "dates": dates, "inst": inst, "desc": desc}


def parse_header_line(line: str, data: dict):
    parts = [p.strip() for p in line.split(SEP) if p.strip()]
    contact = {}
    for i, part in enumerate(parts):
        lm = LINK_ONLY_RE.match(part)
        plain = lm.group(1) if lm else part
        plain = plain.replace("**", "").strip()
        url = lm.group(2) if lm else ""
        if i == 0 and "@" not in plain and "github" not in plain.lower():
            data["tagline"] = plain
        elif "@" in plain:
            contact["email"] = plain
        elif "github.com" in plain.lower() or "github.com" in url.lower():
            contact["github"] = url or ("https://" + plain)
        elif re.search(r"\+?\d[\d\s().-]{7,}", plain):
            contact["phone"] = plain
        elif url.startswith("http"):
            contact["website"] = url
        elif "location" not in contact:
            contact["location"] = plain
    data["contact"] = contact


# --------------------------------------------------------------------------- #
# HTML generation
# --------------------------------------------------------------------------- #

ICON_PIN = '<svg class="contact-icon" viewBox="0 0 24 24"><path d="M12 2C8.13 2 5 5.13 5 9c0 5.25 7 13 7 13s7-7.75 7-13c0-3.87-3.13-7-7-7zm0 9.5c-1.38 0-2.5-1.12-2.5-2.5s1.12-2.5 2.5-2.5 2.5 1.12 2.5 2.5-1.12 2.5-2.5 2.5z"/></svg>'
ICON_MAIL = '<svg class="contact-icon" viewBox="0 0 24 24"><path d="M20 4H4c-1.1 0-1.99.9-1.99 2L2 18c0 1.1.9 2 2 2h16c1.1 0 2-.9 2-2V6c0-1.1-.9-2-2-2zm0 4l-8 5-8-5V6l8 5 8-5v2z"/></svg>'
ICON_PHONE = '<svg class="contact-icon" viewBox="0 0 24 24"><path d="M6.62 10.79c1.44 2.83 3.76 5.14 6.59 6.59l2.2-2.2c.27-.27.67-.36 1.02-.24 1.12.37 2.33.57 3.57.57.55 0 1 .45 1 1V20c0 .55-.45 1-1 1-9.39 0-17-7.61-17-17 0-.55.45-1 1-1h3.5c.55 0 1 .45 1 1 0 1.25.2 2.45.57 3.57.11.35.03.74-.25 1.02l-2.2 2.2z"/></svg>'
ICON_GITHUB = '<svg class="contact-icon" viewBox="0 0 24 24"><path d="M12 2A10 10 0 0 0 2 12c0 4.42 2.87 8.17 6.84 9.5.5.08.66-.23.66-.5v-1.69c-2.77.6-3.36-1.34-3.36-1.34-.46-1.16-1.11-1.47-1.11-1.47-.91-.62.07-.6.07-.6 1 .07 1.53 1.03 1.53 1.03.87 1.52 2.34 1.07 2.91.83.1-.65.35-1.09.63-1.34-2.22-.25-4.55-1.11-4.55-4.92 0-1.11.38-2 1.03-2.71-.1-.25-.45-1.29.1-2.64 0 0 .84-.27 2.75 1.02.79-.22 1.65-.33 2.5-.33.85 0 1.71.11 2.5.33 1.91-1.29 2.75-1.02 2.75-1.02.55 1.35.2 2.39.1 2.64.65.71 1.03 1.6 1.03 2.71 0 3.82-2.34 4.66-4.57 4.91.36.31.69.92.69 1.85V21c0 .27.16.59.67.5C19.14 20.16 22 16.42 22 12A10 10 0 0 0 12 2z"/></svg>'
ICON_WEB = '<svg class="contact-icon" viewBox="0 0 24 24"><path d="M12 2a10 10 0 1 0 0 20 10 10 0 0 0 0-20zm6.9 6h-2.95a15.7 15.7 0 0 0-1.38-3.56A8.03 8.03 0 0 1 18.9 8zM12 4.04c.83 1.2 1.48 2.53 1.91 3.96h-3.82c.43-1.43 1.08-2.76 1.91-3.96zM4.26 14a8.2 8.2 0 0 1 0-4h3.38a16.5 16.5 0 0 0 0 4H4.26zm.82 2h2.95c.32 1.25.78 2.45 1.38 3.56A7.99 7.99 0 0 1 5.08 16zm2.95-8H5.08a7.99 7.99 0 0 1 4.33-3.56A15.7 15.7 0 0 0 8.03 8zM12 19.96A14.7 14.7 0 0 1 10.09 16h3.82A14.7 14.7 0 0 1 12 19.96zM14.34 14H9.66a14.7 14.7 0 0 1 0-4h4.68a14.7 14.7 0 0 1 0 4zm.25 5.56c.6-1.11 1.06-2.31 1.38-3.56h2.95a8.03 8.03 0 0 1-4.33 3.56zM16.36 14a16.5 16.5 0 0 0 0-4h3.38a8.2 8.2 0 0 1 0 4h-3.38z"/></svg>'


def link_or_text(title: str, url: str) -> str:
    inner = format_markdown_inline(title)
    if url:
        return f'<a href="{htmllib.escape(url, quote=False)}" target="_blank">{inner}</a>'
    return inner


def bullets_html(items) -> str:
    if not items:
        return ""
    return '<ul class="bullets">' + "".join(
        f"<li>{format_markdown_inline(t)}</li>" for t in items
    ) + "</ul>"


def section(title: str, body: str) -> str:
    return f'<div class="block"><div class="section-title">{_esc(title)}</div>{body}</div>'


def render_experience(entries) -> str:
    out = []
    for e in entries:
        dates = f'<span class="exp-dates">{_esc(e["dates"])}</span>' if e["dates"] else ""
        sub = f'<div class="exp-sub">{format_markdown_inline(e["sub"])}</div>' if e["sub"] else ""
        out.append(
            f'<div class="exp-entry"><div class="exp-header">'
            f'<span class="exp-title">{link_or_text(e["title"], e["url"])}</span>{dates}</div>'
            f'{sub}{bullets_html(e["bullets"])}</div>'
        )
    return section(SECTION_TITLES["experience"], "".join(out))


def render_builds(builds, hackathons: str, title: str) -> str:
    features = [b for b in builds if b["bullets"]]
    cards = [b for b in builds if not b["bullets"]]
    out = []
    for b in features:
        tagline = f'<span class="build-tagline">{format_markdown_inline(b["tagline"])}</span>' if b["tagline"] else ""
        extras = "".join(
            f'<a class="build-extra" href="{htmllib.escape(u, quote=False)}" target="_blank">{_esc(t)} ↗</a>'
            for t, u in b["extras"]
        )
        out.append(
            f'<div class="build-feature"><div class="build-head">'
            f'<span class="build-title">{link_or_text(b["title"], b["url"])}</span>{tagline}{extras}</div>'
            f'{bullets_html(b["bullets"])}</div>'
        )
    if cards:
        grid = "".join(
            f'<div class="build-card"><div class="build-title">{link_or_text(b["title"], b["url"])}</div>'
            f'<div class="build-sub">{format_markdown_inline(b["tagline"])}</div></div>'
            for b in cards
        )
        out.append(f'<div class="builds-grid">{grid}</div>')
    if hackathons:
        out.append(hackathons_row(hackathons))
    return section(title, "".join(out))


def hackathons_row(text: str, label: bool = True) -> str:
    text = re.sub(r"^\*\*hackathons:?\*\*:?\s*", "", text.strip(), flags=re.I)
    prefix = f"<strong>Hackathons</strong> {SEP} " if label else ""
    return f'<div class="hackathons-row">{prefix}{format_markdown_inline(text)}</div>'


def render_right_sections(data: dict) -> str:
    out = []
    for sec in data["sections"]:
        kind = sec["kind"]
        if kind == "experience" and sec["entries"]:
            out.append(render_experience(sec["entries"]))
        elif kind == "builds":
            out.append(render_builds(sec["builds"], sec["hackathons"], SECTION_TITLES["builds"]))
        elif kind == "other_projects" and sec["builds"]:
            out.append(render_builds(sec["builds"], "", SECTION_TITLES["other_projects"]))
        elif kind == "hackathons" and sec["text"]:
            out.append(section(SECTION_TITLES["hackathons"], hackathons_row(sec["text"], label=False)))
        elif kind == "writing" and sec["lines"]:
            out.append(section(SECTION_TITLES["writing"], bullets_html(sec["lines"])))
        elif kind == "generic" and sec["lines"]:
            out.append(section(sec["heading"], bullets_html(sec["lines"])))
    return "".join(out)


def render_education(entries) -> str:
    out = []
    for e in entries:
        meta = " · ".join(x for x in (e["inst"], e["dates"]) if x)
        out.append(
            f'<div class="edu-entry"><div class="entry-role">{link_or_text(e["title"], e["url"])}</div>'
            + (f'<div class="entry-meta-stacked">{format_markdown_inline(meta)}</div>' if meta else "")
            + (f'<p class="entry-desc">{format_markdown_inline(e["desc"])}</p>' if e["desc"] else "")
            + "</div>"
        )
    return section(SECTION_TITLES["education"], "".join(out))


def render_contact(contact: dict) -> str:
    c = {**DEFAULT_CONTACT, **contact}
    items = []
    if c.get("location"):
        items.append(f'<div class="contact-item">{ICON_PIN}<span>{_esc(c["location"])}</span></div>')
    if c.get("email"):
        e = htmllib.escape(c["email"], quote=False)
        items.append(f'<div class="contact-item">{ICON_MAIL}<span><a href="mailto:{e}">{e}</a></span></div>')
    if c.get("phone"):
        tel = re.sub(r"[^\d+]", "", c["phone"])
        items.append(f'<div class="contact-item">{ICON_PHONE}<span><a href="tel:{tel}">{_esc(c["phone"])}</a></span></div>')
    if c.get("github"):
        url = c["github"] if c["github"].startswith("http") else "https://" + c["github"]
        label = re.sub(r"^https?://", "", url).rstrip("/")
        items.append(f'<div class="contact-item">{ICON_GITHUB}<span><a href="{htmllib.escape(url, quote=False)}" target="_blank">{_esc(label)}</a></span></div>')
    if c.get("website"):
        url = c["website"]
        label = re.sub(r"^https?://", "", url).rstrip("/")
        items.append(f'<div class="contact-item">{ICON_WEB}<span><a href="{htmllib.escape(url, quote=False)}" target="_blank">{_esc(label)}</a></span></div>')
    return "".join(items)


CSS = """
    :root {
      --bg: __BG__;
      --text: __TEXT__;
      --text-muted: __MUTED__;
      --line: __LINE__;
      --card-bg: __CARD_BG__;
      --card-border: __CARD_BORDER__;
    }
    @page { size: A4 portrait; margin: 8mm 9mm; background: __BG__; }
    *, *::before, *::after { box-sizing: border-box; }
    html, body {
      margin: 0; padding: 0;
      background: var(--bg); color: var(--text);
      font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, 'Helvetica Neue', Arial, sans-serif;
      font-size: 10.2pt; line-height: 1.44;
      -webkit-font-smoothing: antialiased;
    }
    a { color: var(--text); text-decoration: underline; text-underline-offset: 2.5px; text-decoration-thickness: 1px; }
    code { font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 0.92em; }

    .cv-container {
      zoom: __ZOOM__;
      border: 1.5px solid var(--line);
      background: var(--bg);
      -webkit-box-decoration-break: clone; box-decoration-break: clone;
    }

    /* HEADER */
    .header-row {
      display: flex; flex-direction: row;
      border-bottom: 1.5px solid var(--line);
      min-height: 164px; break-inside: avoid;
    }
    .header-photo-box {
      width: 155px; min-width: 155px;
      border-right: 1.5px solid var(--line);
      display: flex; align-items: center; justify-content: center;
      padding: 7px; background: __PHOTO_BG__;
    }
    .header-photo { width: 100%; height: 150px; object-fit: cover; object-position: center 20%; display: block; }
    .header-initials { font-size: 34pt; font-weight: 900; letter-spacing: 2px; color: var(--text); }
    .header-content { flex: 1; display: flex; flex-direction: column; justify-content: space-between; padding: 13px 18px 11px 18px; }
    .cv-name { font-size: 34pt; font-weight: 900; letter-spacing: -0.02em; line-height: 0.95; margin: 0; text-transform: uppercase; color: var(--text); }
    .cv-tagline { font-size: 10.2pt; font-weight: 500; color: var(--text-muted); margin-top: 6px; line-height: 1.35; letter-spacing: -0.01em; }
    .contact-grid {
      display: grid; grid-template-columns: 1fr 1fr; row-gap: 5px; column-gap: 16px;
      font-size: 9.8pt; line-height: 1.4;
      border-top: 1px solid var(--line); padding-top: 7px; margin-top: 7px;
    }
    .contact-item { display: flex; align-items: center; gap: 6px; color: var(--text); min-width: 0; }
    .contact-item span { overflow-wrap: anywhere; }
    .contact-icon { width: 13px; height: 13px; flex-shrink: 0; fill: currentColor; }

    /* BODY: two columns; the vertical rule is a background so it continues across pages */
    .body-columns {
      display: flex; flex-direction: row; align-items: stretch;
      background: linear-gradient(to right,
        transparent 0, transparent calc(37% - 0.75px),
        var(--line) calc(37% - 0.75px), var(--line) calc(37% + 0.75px),
        transparent calc(37% + 0.75px));
    }
    .col-left, .col-right {
      -webkit-box-decoration-break: clone; box-decoration-break: clone;
    }
    .col-left { width: 37%; min-width: 37%; padding: 12px 15px; }
    .col-right { flex: 1; min-width: 0; padding: 12px 16px; }
    .block { margin-bottom: 12px; }
    .block:last-child { margin-bottom: 0; }

    .section-title {
      font-size: 10.5pt; font-weight: 900; text-transform: uppercase; letter-spacing: 0.05em;
      margin: 0 0 6px 0; color: var(--text);
      display: flex; align-items: center; gap: 6px;
      break-after: avoid;
    }
    .section-title::after { content: ""; flex: 1; height: 1px; background: var(--line); opacity: 0.25; }

    .bio-text { font-size: 9.8pt; line-height: 1.46; color: var(--text); margin: 0 0 7px 0; text-align: justify; }
    .bio-text:last-child { margin-bottom: 0; }

    .edu-entry { margin-bottom: 9px; break-inside: avoid; }
    .edu-entry:last-child { margin-bottom: 0; }
    .entry-role { font-weight: 800; font-size: 10.2pt; line-height: 1.35; color: var(--text); }
    .entry-meta-stacked { font-size: 9.5pt; font-weight: 600; color: var(--text-muted); margin: 2px 0 3px 0; line-height: 1.35; }
    .entry-desc { font-size: 9.5pt; color: var(--text-muted); line-height: 1.42; margin: 0; }

    .lang-block { font-size: 9.6pt; line-height: 1.48; color: var(--text); }

    .exp-entry { margin-bottom: 8px; break-inside: avoid; }
    .exp-entry:last-child { margin-bottom: 0; }
    .exp-header { display: flex; justify-content: space-between; align-items: baseline; gap: 10px; margin-bottom: 1px; }
    .exp-title { font-size: 10.2pt; font-weight: 800; color: var(--text); }
    .exp-dates { font-size: 9.5pt; font-weight: 700; color: var(--text-muted); white-space: nowrap; }
    .exp-sub { font-size: 9.5pt; font-weight: 600; color: var(--text-muted); line-height: 1.40; margin: 0 0 2px 0; }

    ul.bullets { list-style: none; margin: 2px 0 0 0; padding: 0; }
    ul.bullets li { position: relative; padding-left: 10px; font-size: 9.4pt; color: var(--text-muted); line-height: 1.40; margin: 0 0 1.5px 0; }
    ul.bullets li::before { content: ""; position: absolute; left: 0; top: 0.58em; width: 3.5px; height: 3.5px; background: var(--text); }

    .build-feature, .build-card {
      background: var(--card-bg); border: 1px solid var(--card-border); border-radius: 2px;
      padding: 6px 9px; break-inside: avoid;
    }
    .build-feature { margin-bottom: 7px; }
    .build-feature:last-child { margin-bottom: 0; }
    .build-head { display: flex; flex-wrap: wrap; align-items: baseline; column-gap: 8px; margin-bottom: 2px; }
    .build-title { font-size: 9.8pt; font-weight: 800; color: var(--text); }
    .build-tagline { font-size: 9.2pt; font-weight: 600; color: var(--text-muted); }
    .build-extra { font-size: 9pt; margin-left: auto; color: var(--text); }
    .builds-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 6px 9px; margin-top: 7px; }
    .builds-grid:first-child { margin-top: 0; }
    .build-card { padding: 5px 8px; }
    .build-sub { font-size: 9.2pt; color: var(--text-muted); line-height: 1.32; }

    .hackathons-row {
      font-size: 9.2pt; line-height: 1.40; color: var(--text);
      margin-top: 7px; padding: 4px 7px;
      border-left: 2px solid var(--line); background: var(--card-bg); break-inside: avoid;
    }
    .block > .hackathons-row:first-of-type { margin-top: 0; }

    .skills-bar { border-top: 1.5px solid var(--line); padding: 10px 16px 9px 16px; break-inside: avoid; }
    .skills-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(130px, 1fr)); gap: 12px; }
    .skill-col-title { font-size: 9.8pt; font-weight: 900; text-transform: uppercase; letter-spacing: 0.04em; margin-bottom: 3px; color: var(--text); }
    .skill-col-content { font-size: 9.2pt; line-height: 1.40; color: var(--text-muted); }
    .skill-side { margin-bottom: 7px; break-inside: avoid; }
    .skill-side:last-child { margin-bottom: 0; }
"""


def generate_cv_html(data: dict, photo_b64: str = "", theme_name: str = "warm",
                     skills_layout: str = "bar", zoom: float = 1.0,
                     photo_mime: str = "image/jpeg") -> str:
    """Generates the full styled HTML for the CV."""
    theme = THEMES.get(theme_name, THEMES["warm"])
    name_html = _esc(data["name"])

    if photo_b64:
        photo_html = (f'<div class="header-photo-box"><img class="header-photo" '
                      f'src="data:{photo_mime};base64,{photo_b64}" alt="{name_html}"></div>')
    else:
        initials = "".join(p[0] for p in data["name"].split()[:2]).upper()
        photo_html = f'<div class="header-photo-box"><div class="header-initials">{_esc(initials)}</div></div>'

    # ---- left column
    left = []
    if data["bio"]:
        left.append(section(SECTION_TITLES["bio"],
                            "".join(f'<p class="bio-text">{format_markdown_inline(p)}</p>' for p in data["bio"])))
    if data["skills"] and skills_layout == "sidebar":
        left.append(section(SECTION_TITLES["skills_side"], "".join(
            f'<div class="skill-side"><div class="skill-col-title">{_esc(cat)}</div>'
            f'<div class="skill-col-content">{format_markdown_inline(val)}</div></div>'
            for cat, val in data["skills"])))
    if data["education"]:
        left.append(render_education(data["education"]))
    if data["languages"]:
        left.append(section(SECTION_TITLES["languages"],
                            '<div class="lang-block">' + "".join(
                                f"<div>{format_markdown_inline(l)}</div>" for l in data["languages"]) + "</div>"))

    skills_bar = ""
    if data["skills"] and skills_layout == "bar":
        cols = "".join(
            f'<div><div class="skill-col-title">{_esc(cat)}</div>'
            f'<div class="skill-col-content">{format_markdown_inline(val)}</div></div>'
            for cat, val in data["skills"])
        skills_bar = (f'<div class="skills-bar"><div class="section-title">{_esc(SECTION_TITLES["skills_bar"])}</div>'
                      f'<div class="skills-grid">{cols}</div></div>')

    css = (CSS.replace("__BG__", theme["bg"]).replace("__TEXT__", theme["text"])
           .replace("__MUTED__", theme["text_muted"]).replace("__LINE__", theme["line"])
           .replace("__CARD_BG__", theme["card_bg"]).replace("__CARD_BORDER__", theme["card_border"])
           .replace("__PHOTO_BG__", theme["photo_bg"]).replace("__ZOOM__", f"{zoom:.3f}"))

    return f"""<!DOCTYPE html>
<html lang="{LANG}">
<head>
  <meta charset="utf-8">
  <title>{name_html} - Curriculum Vitae</title>
  <style>{css}</style>
</head>
<body>
  <div class="cv-container">
    <div class="header-row">
      {photo_html}
      <div class="header-content">
        <div>
          <h1 class="cv-name">{name_html}</h1>
          <div class="cv-tagline">{_esc(data.get("tagline") or DEFAULT_TAGLINE)}</div>
        </div>
        <div class="contact-grid">{render_contact(data.get("contact", {}))}</div>
      </div>
    </div>
    <div class="body-columns">
      <div class="col-left">{"".join(left)}</div>
      <div class="col-right">{render_right_sections(data)}</div>
    </div>
    {skills_bar}
  </div>
</body>
</html>
"""


# --------------------------------------------------------------------------- #
# Translation: English markdown -> Portuguese of Portugal (pt-PT)
# --------------------------------------------------------------------------- #

LANG = "en"
SECTION_TITLES_EN = dict(SECTION_TITLES)
SECTION_TITLES_PT = {
    "bio": "Perfil e Visão",
    "skills_bar": "Competências Essenciais e Técnicas",
    "skills_side": "Competências",
    "languages": "Idiomas",
    "education": "Formação",
    "experience": "Experiência e Liderança",
    "builds": "Projetos e Sistemas de IA",
    "other_projects": "Outros Projetos",
    "hackathons": "Hackathons",
    "writing": "Escrita e Media Selecionadas",
}

# Section headings written into the Portuguese markdown (by section type, not machine-translated).
PT_HEADINGS = {
    "experience": "Experiência",
    "education": "Formação",
    "skills": "Competências",
    "builds": "Projetos selecionados",
    "other_projects": "Outros projetos",
    "hackathons": "Hackathons",
    "writing": "Escrita e media selecionadas",
}

# Never translated: names, products, tools, acronyms.
KEEP_TERMS = [
    "AI-OS", "Fusion", "Mentally", "Arta", "Heretically", "Nefilum Web", "NEFilUM", "NIIEM",
    "Amaral Media", "Clínica Sophie Seromenho", "llama.cpp", "llama-server", "Docker", "Podman",
    "Python", "TypeScript", "Rust", "Oh My Pi", "Looker Studio", "MacBook Pro M4",
    "Cerebras x Gemma 4 24Hours", "Cerebras 24Hours", "OpenAI Build Week",
    "Meta Global AI Developer Hackathon", "Agentic Kit", "Bear/Base/Bull", "EV/Revenue",
    "EV/EBITDA", "DCF", "RTP", "Gerador", "Uniarea", "Repo", "LLMs", "LLM",
    "Hackathons", "Hackathon",
]

# English -> final Portuguese, applied before machine translation (official names, fixed phrases).
# Add your own with --glossary file.json  ({"english phrase": "frase em português"}).
FIXED_TERMS = {
    "University of Minho": "Universidade do Minho",
    "Secondary school D. Maria II": "Escola Secundária D. Maria II",
    "Secondary School D. Maria II": "Escola Secundária D. Maria II",
    "BA Philosophy": "Licenciatura em Filosofia",
    "Philosophy Student Association": "Núcleo de Estudantes de Filosofia",
    "Association for Research & Intervention in Emotional Education":
        "Núcleo de Investigação e Intervenção na Educação Emocional",
    "Languages": "Idiomas",
}


def normalise_lang(code: str) -> str:
    c = code.strip().lower().replace("_", "-")
    if c in ("en", "en-us", "en-gb"):
        return "en"
    if c in ("pt", "pt-pt", "ptpt"):
        return "pt-PT"
    raise ValueError(f"Unsupported language '{code}'. Use en or pt-PT.")


def set_language(lang: str):
    global LANG
    LANG = lang
    SECTION_TITLES.clear()
    SECTION_TITLES.update(SECTION_TITLES_PT if lang == "pt-PT" else SECTION_TITLES_EN)


def localise_pt(text: str) -> str:
    """pt-PT number conventions: 16.03 -> 16,03 and 4,000 -> 4000."""
    text = re.sub(r"(?<=\d),(?=\d{3}(?!\d))", "", text)
    return re.sub(r"(?<=\d)\.(?=\d)", ",", text)


# ---- tokenising: what must never reach the translator ---------------------- #

LINE_RE = re.compile(r"^(\s*(?:#{1,6}\s+|[-*+]\s+)?)(.*)$", re.S)
HAS_LETTER = re.compile(r"[^\W\d_]")
CORE_RE = re.compile(r"^([\s,;:.()\-–—]*)(.*?)([\s,;:()\-–—]*)$", re.S)


def make_token_re(terms):
    alts = [
        r"(?P<code>`[^`]+`)",
        r"(?P<target>\]\([^)\s]+\))",
        r"(?P<url>https?://[^\s)\]]+)",
        r"(?P<mail>[\w.+-]+@[\w-]+(?:\.[\w-]+)+)",
        r"(?P<dom>\b[\w-]+\.(?:com|io|dev|pt|eu|org|net|app|ai|me)\b(?:/[^\s)\]]*)?)",
        r"(?P<ital>(?<![\*\w])\*(?!\s)[^*\n]+?(?<!\s)\*(?![\*\w]))",  # *titles* stay as written
        r"(?P<bold>\*\*)",
        r"(?P<br>\[)",
        r"(?P<sep>\s+◦\s+)",
        r"(?P<ay>\bAY\s+\d{4}(?:[–-]\d{2,4})?)",
        r"(?P<yr>\(\d{4}(?:[–-]\d{2,4})?\))",
    ]
    if terms:
        body = "|".join(re.escape(t) for t in sorted(terms, key=len, reverse=True))
        alts.append(r"(?P<term>(?<!\w)(?:" + body + r")(?!\w))")
    return re.compile("|".join(alts))


def tokenise(text, token_re, fixed):
    """-> list of (is_protected, text); adjacent protected pieces are merged."""
    toks, pos = [], 0

    def add(raw, s):
        if raw and toks and toks[-1][0]:
            toks[-1] = (True, toks[-1][1] + s)
        else:
            toks.append((raw, s))

    for m in token_re.finditer(text):
        if m.start() > pos:
            add(False, text[pos:m.start()])
        s, g = m.group(0), m.lastgroup
        if g == "ay":
            s = re.sub(r"^AY\s+", "ano letivo ", s)
        elif g == "term":
            s = fixed.get(s, s)
        add(True, s)
        pos = m.end()
    if pos < len(text):
        add(False, text[pos:])
    return toks


def to_tagged(toks):
    return "".join(
        f"<x>{htmllib.escape(t, quote=False)}</x>" if raw else htmllib.escape(t, quote=False)
        for raw, t in toks)


def from_tagged(out):
    res = []
    for p in re.split(r"(<x>.*?</x>)", out, flags=re.S):
        if p.startswith("<x>") and p.endswith("</x>"):
            res.append((True, htmllib.unescape(p[3:-4])))
        elif p:
            res.append((False, htmllib.unescape(p)))
    return res


def segment_parts(toks):
    """Translatable pieces for engines without tag support: (index, lead, core, trail)."""
    parts = []
    for k, (raw, t) in enumerate(toks):
        if raw or not HAS_LETTER.search(t):
            continue
        lead, core, trail = CORE_RE.match(t).groups()
        if HAS_LETTER.search(core):
            parts.append((k, lead, core, trail))
    return parts


# ---- engines ---------------------------------------------------------------- #

def _http_json(url, data=None, headers=None, timeout=90):
    req = urllib.request.Request(url, data=data, headers=headers or {})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        body = e.read().decode("utf-8", "replace")[:300]
        hint = {403: " (check DEEPL_API_KEY)", 456: " (DeepL quota exhausted)"}.get(e.code, "")
        raise RuntimeError(f"HTTP {e.code} from {url}{hint}: {body}") from None
    except urllib.error.URLError as e:
        raise RuntimeError(f"cannot reach {url}: {e.reason}") from None


class Translator:
    name = ""
    tags = False  # True when the engine can pass <x>...</x> content through untouched

    def translate(self, texts, tagged):
        raise NotImplementedError


class DeepLTranslator(Translator):
    name, tags = "deepl", True

    def __init__(self):
        self.key = os.environ.get("DEEPL_API_KEY", "").strip()
        if not self.key:
            raise RuntimeError("DEEPL_API_KEY is not set (a free key works: https://www.deepl.com/pro-api)")
        host = "api-free.deepl.com" if self.key.endswith(":fx") else "api.deepl.com"
        self.url = os.environ.get("DEEPL_API_URL") or f"https://{host}/v2/translate"

    def translate(self, texts, tagged):
        out = []
        for i in range(0, len(texts), 40):
            pairs = [("text", t) for t in texts[i:i + 40]]
            pairs += [("source_lang", "EN"), ("target_lang", "PT-PT"), ("preserve_formatting", "1")]
            if tagged:
                pairs += [("tag_handling", "xml"), ("ignore_tags", "x")]
            reply = _http_json(
                self.url, urllib.parse.urlencode(pairs).encode(),
                {"Authorization": f"DeepL-Auth-Key {self.key}",
                 "Content-Type": "application/x-www-form-urlencoded"})
            out += [t["text"] for t in reply["translations"]]
        return out


LLM_SYSTEM = (
    "You translate CV text from English into European Portuguese (pt-PT, as written in Portugal), "
    "never Brazilian Portuguese. Use Portugal vocabulary and forms (equipa, utilizador, ecrã, gerir; "
    "'estou a fazer', not 'estou fazendo') and the 1990 orthographic agreement. Keep a concise, "
    "professional CV register, in the first person or impersonal as the source does. Keep proper "
    "nouns, product names, tool names and acronyms unchanged. Reply with the translation only: "
    "no quotes, no notes, no explanations."
)
LLM_TAG_RULE = (" The text contains <x>...</x> tags: copy every tag and everything inside it exactly "
                "as given, untranslated, and keep every tag in the output.")


class LLMTranslator(Translator):
    """Any OpenAI-compatible chat endpoint (llama-server, llama-swap, Ollama, LM Studio...)."""
    name, tags = "llm", True

    def __init__(self, base_url, model=""):
        self.base = base_url.rstrip("/")
        self.headers = {"Content-Type": "application/json"}
        if os.environ.get("LLM_API_KEY"):
            self.headers["Authorization"] = "Bearer " + os.environ["LLM_API_KEY"]
        try:
            models = _http_json(self.base + "/models", headers=self.headers, timeout=3)
        except RuntimeError as e:
            raise RuntimeError(f"no local LLM server at {self.base} ({e})") from None
        if not model:
            ids = [m.get("id") for m in models.get("data", []) if m.get("id")]
            model = ids[0] if ids else "default"
        self.model = model

    def translate(self, texts, tagged):
        system = LLM_SYSTEM + (LLM_TAG_RULE if tagged else "")
        out = []
        for t in texts:
            payload = {"model": self.model, "temperature": 0, "max_tokens": 1500, "stream": False,
                       "messages": [{"role": "system", "content": system},
                                    {"role": "user", "content": t}]}
            reply = _http_json(self.base + "/chat/completions", json.dumps(payload).encode(),
                               self.headers, timeout=300)
            text = reply["choices"][0]["message"]["content"] or ""
            text = re.sub(r"<think>.*?</think>", "", text, flags=re.S).strip()
            if len(text) > 1 and text[0] == text[-1] and text[0] in "\"“”'":
                text = text[1:-1].strip()
            out.append(text)
        return out


class ArgosTranslator(Translator):
    """Free, offline. Generic Portuguese (not specifically pt-PT): proofread the result."""
    name = "argos"

    def __init__(self):
        try:
            import argostranslate.package as pkg
            import argostranslate.translate as tr
        except ImportError:
            raise RuntimeError("Argos Translate is not installed (pip install argostranslate)") from None
        self.tr = tr
        try:
            installed = {(l.code, t.to_lang.code) for l in tr.get_installed_languages()
                         for t in l.translations_from}
            if ("en", "pt") not in installed:
                print("Downloading the Argos English->Portuguese model (one-off)...")
                pkg.update_package_index()
                match = next((p for p in pkg.get_available_packages()
                              if p.from_code == "en" and p.to_code == "pt"), None)
                if match is None:
                    raise RuntimeError("no English->Portuguese Argos model is available")
                pkg.install_from_path(match.download())
        except RuntimeError:
            raise
        except Exception as err:  # offline, blocked download, broken install...
            raise RuntimeError(f"could not set up the Argos en->pt model ({err}); "
                               "it needs internet access once to download") from None

    def translate(self, texts, tagged):
        return [self.tr.translate(t, "en", "pt") for t in texts]


def make_translator(args):
    choice = args.translator
    base = args.llm_url or os.environ.get("LLM_BASE_URL") or "http://localhost:8080/v1"
    model = args.llm_model or os.environ.get("LLM_MODEL", "")
    failures = []
    for name in (["deepl", "llm", "argos"] if choice == "auto" else [choice]):
        try:
            if name == "deepl":
                return DeepLTranslator()
            if name == "llm":
                return LLMTranslator(base, model)
            return ArgosTranslator()
        except RuntimeError as err:
            if choice != "auto":
                raise
            failures.append(f"  - {name}: {err}")
    raise RuntimeError(
        "No translation engine available:\n" + "\n".join(failures) +
        "\nSet DEEPL_API_KEY, start a local LLM server, or pip install argostranslate "
        "- or write the .pt-PT.md file yourself.")


class TranslationSession:
    """Batches requests and remembers every result on disk, so re-runs cost nothing."""

    def __init__(self, translator, cache_path):
        self.t, self.path, self.cache = translator, cache_path, {}
        try:
            with open(cache_path, encoding="utf-8") as f:
                self.cache = json.load(f)
        except (OSError, ValueError):
            pass

    def _key(self, text, tagged):
        return f"{self.t.name}|{int(tagged)}|{text}"

    def resolve(self, texts, tagged):
        todo = [t for t in dict.fromkeys(texts) if self._key(t, tagged) not in self.cache]
        for i in range(0, len(todo), 40):
            chunk = todo[i:i + 40]
            for src, out in zip(chunk, self.t.translate(chunk, tagged)):
                self.cache[self._key(src, tagged)] = out
            try:
                with open(self.path, "w", encoding="utf-8") as f:
                    json.dump(self.cache, f, ensure_ascii=False, indent=0)
            except OSError:
                pass
        return [self.cache[self._key(t, tagged)] for t in texts]


def translate_markdown(md_text, session, glossary=None):
    """Translates a CV markdown file to pt-PT, leaving structure, links, names and titles intact."""
    fixed = {**FIXED_TERMS, **(glossary or {})}
    token_re = make_token_re(set(KEEP_TERMS) | set(fixed))
    lines = md_text.splitlines()
    out, plans = list(lines), {}

    for i, line in enumerate(lines):
        s = line.strip()
        if not s or s == "---" or re.match(r"^#\s", s) or s.startswith("|"):
            continue
        if re.match(r"^\*\*skills:?\*\*:?$", s, re.I):
            out[i] = "**Competências:**"
            continue
        h = re.match(r"^(#{2,3})\s+(.*\S)\s*$", s)
        if h:
            kind = classify_heading(h.group(2))
            if kind in PT_HEADINGS and (len(h.group(1)) == 2 or is_section_heading(h.group(2))):
                title = PT_HEADINGS[kind]
                if kind == "builds" and "select" not in h.group(2).lower():
                    title = "Projetos"
                out[i] = f"{h.group(1)} {title}"
                continue
        prefix, body = LINE_RE.match(line).groups()
        toks = tokenise(body, token_re, fixed)
        if any(not raw and HAS_LETTER.search(t) for raw, t in toks):
            plans[i] = (prefix, toks)

    results, fallback = {}, []
    if session.t.tags:
        order = list(plans)
        outs = session.resolve([to_tagged(plans[i][1]) for i in order], True)
        for i, o in zip(order, outs):
            back = from_tagged(o) if o else []
            same = Counter(t for r, t in back if r) == Counter(t for r, t in plans[i][1] if r)
            if back and same:
                results[i] = back
            else:
                fallback.append(i)
    else:
        fallback = list(plans)

    if fallback:
        if session.t.tags:
            print(f"  ({len(fallback)} line(s) came back with damaged markup; translated piecewise instead)")
        parts = {i: segment_parts(plans[i][1]) for i in fallback}
        cores = [c for i in fallback for (_, _, c, _) in parts[i]]
        outs = iter(session.resolve(cores, False))
        for i in fallback:
            toks = list(plans[i][1])
            for k, lead, core, trail in parts[i]:
                toks[k] = (False, lead + next(outs).strip() + trail)
            results[i] = toks

    for i, toks in results.items():
        text = "".join(t if raw else localise_pt(t) for raw, t in toks)
        out[i] = plans[i][0] + re.sub(r"(?<=\S) {2,}", " ", text)
    return "\n".join(out) + "\n"


def resolve_markdown(input_file, lang, args):
    """Markdown file to render for `lang`: the input itself, or its (cached) pt-PT translation."""
    stem = os.path.splitext(input_file)[0]
    if lang == "en" or stem.endswith(".pt-PT"):
        return input_file
    target = stem + ".pt-PT.md"
    if os.path.exists(target) and not args.retranslate:
        print(f"Using existing Portuguese text: {target} (edit it freely; --retranslate regenerates it)")
        return target
    translator = make_translator(args)
    glossary = {}
    if args.glossary:
        with open(args.glossary, encoding="utf-8") as f:
            glossary = json.load(f)
    print(f"Translating to Portuguese (Portugal) with {translator.name}...")
    session = TranslationSession(translator, os.path.join(os.path.dirname(input_file) or ".",
                                                          ".cv-translation-cache.json"))
    with open(input_file, encoding="utf-8") as f:
        text = translate_markdown(f.read(), session, glossary)
    with open(target, "w", encoding="utf-8") as f:
        f.write(text)
    print(f"Wrote {target}. Proofread it before sending: machine translation of a CV needs a human pass.")
    return target


# --------------------------------------------------------------------------- #
# PDF rendering
# --------------------------------------------------------------------------- #

def count_pdf_pages(pdf_bytes: bytes):
    n = len(re.findall(rb"/Type\s*/Page(?![A-Za-z])", pdf_bytes))
    return n or None


def find_chrome() -> str:
    candidates = [os.environ.get("CHROME_BIN", "")]
    for exe in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser", "chrome"):
        candidates.append(shutil.which(exe) or "")
    candidates += [
        "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
        "/Applications/Chromium.app/Contents/MacOS/Chromium",
        r"C:\Program Files\Google\Chrome\Application\chrome.exe",
    ]
    for c in candidates:
        if c and os.path.exists(c):
            return c
    raise RuntimeError("Chrome/Chromium not found (set CHROME_BIN to its path).")


class SeleniumPrinter:
    """Prints HTML strings to PDF bytes through one headless Chrome (Selenium + CDP)."""

    def __init__(self):
        from selenium import webdriver
        from selenium.webdriver.chrome import options as chrome_options
        from selenium.webdriver.chrome import service as chrome_service

        self.profile_dir = tempfile.mkdtemp(prefix="cv_profile_")
        opts = chrome_options.Options()
        for arg in ("--headless=new", "--no-sandbox", "--disable-dev-shm-usage", "--disable-gpu",
                    "--disable-extensions", "--no-first-run", "--no-default-browser-check",
                    f"--user-data-dir={self.profile_dir}", f"--crash-dumps-dir={self.profile_dir}"):
            opts.add_argument(arg)
        xdg_config = os.path.join(self.profile_dir, ".config")
        os.makedirs(os.path.join(xdg_config, "chromium", "Crash Reports"), exist_ok=True)
        env = {**os.environ, "HOME": self.profile_dir, "XDG_CONFIG_HOME": xdg_config}
        driver_path = os.environ.get("CHROMEDRIVER")
        service = (chrome_service.Service(executable_path=driver_path, env=env)
                   if driver_path else chrome_service.Service(env=env))
        try:
            self.driver = webdriver.Chrome(options=opts, service=service)
        except Exception:
            shutil.rmtree(self.profile_dir, ignore_errors=True)
            raise

    def print_html(self, html_text: str) -> bytes:
        self.driver.get("about:blank")
        frame_id = self.driver.execute_cdp_cmd("Page.getFrameTree", {})["frameTree"]["frame"]["id"]
        self.driver.execute_cdp_cmd("Page.setDocumentContent", {"frameId": frame_id, "html": html_text})
        time.sleep(1.0)
        result = self.driver.execute_cdp_cmd("Page.printToPDF", {
            "landscape": False, "displayHeaderFooter": False, "printBackground": True,
            "preferCSSPageSize": True,
            "marginTop": 0, "marginBottom": 0, "marginLeft": 0, "marginRight": 0,
        })
        if not result or "data" not in result:
            raise RuntimeError("Page.printToPDF did not return PDF data")
        return base64.b64decode(result["data"])

    def close(self):
        try:
            self.driver.quit()
        finally:
            shutil.rmtree(self.profile_dir, ignore_errors=True)


class ChromeCliPrinter:
    """Same interface, but calls the Chrome binary directly (no Selenium / chromedriver)."""

    def __init__(self):
        self.chrome = find_chrome()
        self.work = tempfile.mkdtemp(prefix="cv_chrome_")

    def print_html(self, html_text: str) -> bytes:
        html_path = os.path.join(self.work, "cv.html")
        pdf_path = os.path.join(self.work, "cv.pdf")
        with open(html_path, "w", encoding="utf-8") as f:
            f.write(html_text)
        if os.path.exists(pdf_path):
            os.remove(pdf_path)
        cmd = [self.chrome, "--headless=new", "--no-sandbox", "--disable-gpu", "--disable-dev-shm-usage",
               "--no-first-run", "--no-default-browser-check", "--disable-extensions",
               f"--user-data-dir={os.path.join(self.work, 'profile')}",
               "--no-pdf-header-footer", f"--print-to-pdf={pdf_path}",
               "file://" + html_path.replace(os.sep, "/")]
        subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, timeout=120)
        if not os.path.exists(pdf_path):
            raise RuntimeError("Chrome did not produce a PDF")
        with open(pdf_path, "rb") as f:
            return f.read()

    def close(self):
        shutil.rmtree(self.work, ignore_errors=True)


def make_printer(engine: str):
    if engine in ("auto", "selenium"):
        try:
            return SeleniumPrinter()
        except Exception as err:
            if engine == "selenium":
                raise
            first_line = str(err).strip().splitlines()[0] if str(err).strip() else type(err).__name__
            print(f"Selenium unavailable ({first_line[:110]}); using Chrome directly.")
    return ChromeCliPrinter()


def render_best(data, printer, theme, photo_b64, photo_mime, skills_mode, min_zoom):
    """Tries layouts until the CV fits one page; otherwise falls back to a clean two-page flow."""
    layouts = ["bar", "sidebar"] if skills_mode == "auto" else [skills_mode]
    zooms = [z for z in (1.0, 0.98, 0.96, 0.94, 0.92, 0.90, 0.88, 0.86, 0.84, 0.82,
                                       0.80, 0.78, 0.76) if z >= min_zoom - 1e-9] or [1.0]
    last = None
    for zoom in zooms:
        for layout in layouts:
            html_text = generate_cv_html(data, photo_b64, theme, layout, zoom, photo_mime)
            pdf = printer.print_html(html_text)
            pages = count_pdf_pages(pdf)
            last = (pdf, layout, zoom, pages)
            if pages in (1, None):
                return pdf, layout, zoom, pages
    # Does not fit one page: use the balanced flowing layout at full size.
    layout = "sidebar" if skills_mode == "auto" and data["skills"] else layouts[-1]
    html_text = generate_cv_html(data, photo_b64, theme, layout, 1.0, photo_mime)
    pdf = printer.print_html(html_text)
    return pdf, layout, 1.0, count_pdf_pages(pdf)


def main():
    parser = argparse.ArgumentParser(description="Convert Markdown CV to high-end PDF CV")
    parser.add_argument("input", help="Path to input markdown CV file")
    parser.add_argument("output", nargs="?", default="", help="Path to output PDF file (optional)")
    parser.add_argument("--photo", default="", help="Path to profile photo (JPEG/PNG)")
    parser.add_argument("--theme", choices=["warm", "dark", "clean"], default="warm", help="Color theme")
    parser.add_argument("--skills", choices=["auto", "bar", "sidebar"], default="auto",
                        help="Where skills go: bottom bar, left sidebar, or auto (default)")
    parser.add_argument("--min-zoom", type=float, default=0.86,
                        help="Smallest scale used to squeeze onto one page (1 = never shrink)")
    parser.add_argument("--engine", choices=["auto", "selenium", "chrome"], default="auto",
                        help="PDF engine: Selenium, direct Chrome, or auto (Selenium, then Chrome)")
    parser.add_argument("--html", default="", help="Also save the final HTML here (for debugging)")
    parser.add_argument("--lang", default="en",
                        help="Language(s) to render, comma-separated: en, pt-PT (e.g. en,pt-PT)")
    parser.add_argument("--translator", choices=["auto", "deepl", "llm", "argos"], default="auto",
                        help="Engine for the pt-PT translation (auto: DeepL, then local LLM, then Argos)")
    parser.add_argument("--llm-url", default="", help="OpenAI-compatible base URL (default: $LLM_BASE_URL "
                                                      "or http://localhost:8080/v1)")
    parser.add_argument("--llm-model", default="", help="Model name for --translator llm (default: $LLM_MODEL "
                                                        "or the server's first model)")
    parser.add_argument("--glossary", default="", help="JSON file of extra fixed translations "
                                                       '{"english phrase": "frase em português"}')
    parser.add_argument("--retranslate", action="store_true",
                        help="Regenerate <name>.pt-PT.md even if it already exists (overwrites your edits)")

    args = parser.parse_args()

    input_file = os.path.abspath(args.input)
    if not os.path.exists(input_file):
        print(f"Error: input file '{input_file}' not found.")
        sys.exit(1)

    try:
        langs = list(dict.fromkeys(normalise_lang(c) for c in args.lang.split(",") if c.strip()))
    except ValueError as err:
        parser.error(str(err))
    in_stem = os.path.splitext(input_file)[0]
    if in_stem.endswith(".pt-PT") and args.lang == "en":
        langs = ["pt-PT"]  # the input is already the Portuguese file

    def out_path(base, lang, ext):
        """Output file for a language; non-English gets a .pt-PT suffix unless it is the only one."""
        stem = os.path.splitext(base)[0]
        if lang == "en" or len(langs) == 1 or stem.endswith(".pt-PT"):
            return stem + ext
        return f"{stem}.{lang}{ext}"

    default_out = (args.output and os.path.abspath(args.output)) or in_stem + ".pdf"
    if not args.output and in_stem.endswith(".pt-PT") is False and langs == ["pt-PT"]:
        default_out = in_stem + ".pt-PT.pdf"

    photo_b64, photo_mime = "", "image/jpeg"
    if args.photo and os.path.exists(args.photo):
        with open(args.photo, "rb") as pf:
            photo_b64 = base64.b64encode(pf.read()).decode("utf-8")
        photo_mime = mimetypes.guess_type(args.photo)[0] or "image/jpeg"

    printer = make_printer(args.engine)
    try:
        for lang in langs:
            try:
                md_file = resolve_markdown(input_file, lang, args)
            except RuntimeError as err:
                print(f"Error ({lang}): {err}")
                sys.exit(1)
            set_language(lang)
            with open(md_file, "r", encoding="utf-8") as f:
                data = parse_markdown_cv(f.read())

            output_file = out_path(default_out, lang, ".pdf")
            print(f"Compiling '{md_file}' -> '{output_file}' (theme: {args.theme}, language: {lang})...")
            pdf, layout, zoom, pages = render_best(
                data, printer, args.theme, photo_b64, photo_mime, args.skills, args.min_zoom)
            if args.html:
                with open(out_path(os.path.abspath(args.html), lang, ".html"), "w", encoding="utf-8") as hf:
                    hf.write(generate_cv_html(data, photo_b64, args.theme, layout, zoom, photo_mime))
            with open(output_file, "wb") as f:
                f.write(pdf)
            page_txt = f"{pages} page{'s' if pages != 1 else ''}" if pages else "page count unknown"
            print(f"Success! Output PDF generated: {output_file} ({page_txt}, skills: {layout}, scale: {zoom:g})")
            if pages and pages > 1:
                print("Note: content does not fit one page even at the minimum scale; it flows onto "
                      f"{pages} pages. Trim the markdown or lower --min-zoom to compress further.")
    finally:
        printer.close()


if __name__ == "__main__":
    main()
