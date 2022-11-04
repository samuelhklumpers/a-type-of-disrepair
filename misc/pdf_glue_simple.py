import os

from PIL import Image
from misctools import *

def glue(dir, dst):
    fns = os.listdir(dir)
    ims = [Image.open(os.path.join(dir, fn)) for fn in fns if is_image(fn)]
    
    for i, im in enumerate(ims):
        if im.mode == "RGBA":
            ims[i] = im.convert("RGB")

    im, ims = ims[0], ims[1:]
    im.save("glued.pdf", save_all=True, append_images=ims)

if __name__ == "__main__":
    glue(".", "glued.pdf")