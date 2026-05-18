#!/usr/bin/env python3
"""Patch depgraph.py to add height=1.0, width=1.0 to graph nodes."""
import plastexdepgraph

depgraph_path = plastexdepgraph.__file__.replace("__init__.py", "Packages/depgraph.py")
with open(depgraph_path, "r") as f:
    content = f.read()

# Patch first add_node (with fillcolor)
content = content.replace(
    "label=node.id.split(':')[-1],\n                               shape=",
    "label=node.id.split(':')[-1],\n                               height=1.0,\n                               width=1.0,\n                               shape="
)
# Patch second add_node (without fillcolor)
content = content.replace(
    "label=node.id.split(':')[-1],\n               style=style,\n               color=color,",
    "label=node.id.split(':')[-1],\n               height=1.0,\n               width=1.0,\n               style=style,\n               color=color,"
)

with open(depgraph_path, "w") as f:
    f.write(content)
