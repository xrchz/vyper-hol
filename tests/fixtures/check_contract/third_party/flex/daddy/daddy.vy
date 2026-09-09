#pragma version 0.5.0a3

"""
@title Daddy
@license GNU AGPLv3
@author Flex
@notice Protocol owner with a generalized execute function
"""

# ============================================================================================
# Events
# ============================================================================================


event PendingOwnershipTransfer:
    old_owner: address
    new_owner: address

event OwnershipTransferred:
    old_owner: address
    new_owner: address


# ============================================================================================
# Constants
# ============================================================================================


_MAX_RETURN_SIZE: constant(uint256) = 8192


# ============================================================================================
# Storage
# ============================================================================================


owner: public(address)
pending_owner: public(address)


# ============================================================================================
# Constructor
# ============================================================================================


@deploy
def __init__(owner: address):
    """
    @notice Initialize the contract
    @param owner Address of owner
    """
    # Set owner
    self.owner = owner

    # Emit event
    log OwnershipTransferred(
        old_owner=empty(address),
        new_owner=owner,
    )


# ============================================================================================
# Receive Ether
# ============================================================================================


@external
@payable
def __default__():
    pass


# ============================================================================================
# Ownership
# ============================================================================================


@external
def transfer_ownership(new_owner: address):
    """
    @notice Starts the ownership transfer of the contract to a new account
    @dev Only callable by the owner
    @dev Replaces the pending transfer if there is one
    @param new_owner The address of the new owner
    """
    assert msg.sender == self.owner, "!owner"

    self.pending_owner = new_owner

    log PendingOwnershipTransfer(
        old_owner=self.owner,
        new_owner=new_owner,
    )


@external
def accept_ownership():
    """
    @notice The new owner accepts the ownership transfer
    @dev Only callable by the current `pending_owner`
    """
    assert self.pending_owner == msg.sender, "!pending_owner"

    self.pending_owner = empty(address)

    old_owner: address = self.owner
    self.owner = msg.sender

    log OwnershipTransferred(
        old_owner=old_owner,
        new_owner=msg.sender,
    )


# ============================================================================================
# Execute
# ============================================================================================


@external
@payable
def execute(
    target: address,
    data: Bytes[_MAX_RETURN_SIZE],
    eth_value: uint256 = 0,
    revert_on_failure: bool = True,
) -> Bytes[_MAX_RETURN_SIZE]:
    """
    @notice Execute an arbitrary call
    @dev Only callable by the owner
    @param target The address to call
    @param data The calldata to send
    @param eth_value The ETH value to send. Defaults to 0
    @param revert_on_failure Whether to revert on failure. Defaults to True
    @return response The return data from the call
    """
    assert msg.sender == self.owner, "!owner"

    success: bool = False
    response: Bytes[_MAX_RETURN_SIZE] = b""
    success, response = raw_call(
        target,
        data,
        max_outsize=_MAX_RETURN_SIZE,
        value=eth_value,
        revert_on_failure=False,
    )

    assert success or not revert_on_failure, "call failed"

    return response
