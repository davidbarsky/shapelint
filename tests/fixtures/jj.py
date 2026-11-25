#!/usr/bin/env python3
import json
import pathlib
import sys

pathlib.Path("jj-arguments.json").write_text(json.dumps(sys.argv[1:]))
if "--template" in sys.argv:
    print(json.dumps("file.rs"))
else:
    sys.stdout.write(pathlib.Path("jj-output.patch").read_text())
