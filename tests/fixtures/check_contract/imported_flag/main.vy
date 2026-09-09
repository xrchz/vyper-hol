import lib

@external
def is_admin(role: lib.Roles) -> bool:
    return role in lib.Roles.ADMIN
