import lib

@external
def sum_point(p: lib.Point) -> uint256:
    return p.x + p.y
