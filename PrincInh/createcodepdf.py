#!/usr/bin/env python3

import os

with open("../_CoqProject") as CoqProjectfile:
    filelist = [name[9:-1] for name in CoqProjectfile.readlines()[2:]]

for fname in filelist:
    with open("code.tex") as codetexfile:
        codetex = codetexfile.read().replace("XXXX", fname)
        texname = fname[:-2] + ".tex"
        with open(texname, "w") as f:
            f.write(codetex)
        os.system("lualatex --shell-escape {}".format(texname))


