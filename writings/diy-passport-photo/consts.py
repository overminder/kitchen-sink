VG_W = 101.6
VG_H = 152.4

V_W = 33
V_H = 48

DP_MM = 11.81

# mm to dots (pixels)
def m2d(*x):
    if len(x) == 2:
        return m2d(x[0]), m2d(x[1])
    return int(x[0] * DP_MM)

def test():
    print('dots w/h', VG_W * DP_MM, VG_H * DP_MM)
