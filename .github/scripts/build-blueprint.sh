#!/bin/sh
# Run from the repository root inside the TeXLive Alpine image.
set -eu

apk update
apk add --update make py3-pip git pkgconfig graphviz graphviz-dev gcc musl-dev
git config --global --add safe.directory "${GITHUB_WORKSPACE:-$PWD}"
git config --global --add safe.directory "$PWD"

# -L only affects linking. Alpine installs Graphviz plugins outside the
# dynamic loader's default search path; pygraphviz also needs them at runtime.
export LD_LIBRARY_PATH="/usr/lib/graphviz${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"

python3 -m venv env
. env/bin/activate
python3 -m pip install --upgrade pip requests wheel
CFLAGS="-I/usr/include/graphviz" LDFLAGS="-L/usr/lib/graphviz" python3 -m pip install pygraphviz
python3 -m pip install leanblueprint

# Fail directly on import/render errors. plasTeX can log an ImportError and
# still exit successfully, leaving HTML without any blueprint metadata.
python3 - <<'PY'
import importlib.metadata as metadata
from pathlib import Path
from tempfile import TemporaryDirectory
import pygraphviz as p
import leanblueprint.Packages.blueprint

print({name: metadata.version(name) for name in ("leanblueprint", "plasTeX", "pygraphviz")})
graph = p.AGraph(directed=True)
graph.add_edge("a", "b")
with TemporaryDirectory() as directory:
    output = Path(directory) / "graph.svg"
    graph.draw(str(output), prog="dot", format="svg")
    assert output.stat().st_size > 0, "Graphviz produced an empty SVG"
PY

leanblueprint pdf
test -s blueprint/print/print.pdf
leanblueprint web
test -s blueprint/lean_decls
test -s blueprint/web/index.html
test -s blueprint/web/dep_graph_document.html

mkdir -p home_page
cp blueprint/print/print.pdf home_page/blueprint.pdf
cp -r blueprint/web home_page/blueprint
