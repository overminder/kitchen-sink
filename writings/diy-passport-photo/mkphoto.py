from PIL import Image, ImageColor, ImageDraw, ImageFont
import os

from consts import *

def calc_margins(vg_w, vg_h, v_w, v_h, n):
    n_w, n_h = n
    assert vg_w - v_w * n_w > 0
    assert vg_h - v_h * n_h > 0
    return ((vg_w - v_w * n_w) / (n_w + 1),
            (vg_h - v_h * n_h) / (n_h + 1))

def populate_container(orig, container, v, n, margins):
    m_w, m_h = margins
    v_w, v_h = v
    n_w, n_h = n
    for dy in range(n_h):
        y = m2d(m_h + dy * (m_h + v_h))
        for dx in range(n_w):
            x = m2d(m_w + dx * (m_w + v_w))
            container.paste(orig, (x, y))

def once(orig, v_w, v_h, label, out):
    orig = orig.resize(m2d(v_w, v_h), Image.LANCZOS)
    container = Image.new('RGB', m2d(VG_W, VG_H), 'white')

    N = (2, 2)
    margins = calc_margins(VG_W, VG_H, v_w, v_h, N)
    populate_container(orig, container, (v_w, v_h), N, margins)

    kbd = ImageFont.truetype('Comic Sans MS.ttf', 48)
    d = ImageDraw.Draw(container)
    d.text((0, 0), label, fill='black', font=kbd)

    container.save(out, dpi=(300, 300))

def main():
    orig = Image.open(os.path.expanduser('~/Downloads/IMG_6468.JPG'))
    for i, ratio in enumerate((0.98, 0.99, 1, 1.01, 1.02)):
        outdir = os.path.expanduser('~/Downloads/out')
        once(orig, V_W * ratio, V_H * ratio, str(ratio), f'{outdir}/{i}.png')

if __name__ == '__main__':
    main()

