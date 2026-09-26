/*
 * Sell order: seller cancels with signature, or anyone spends if OUTPUTS(0) pays the seller >= price.
 *
 * @param sellerPk Seller public key
 * @param sellerProp Seller proposition bytes
 * @param price Minimum nanoERG paid to seller
 */
@contract def sellOrder(sellerPk: GroupElement, sellerProp: Coll[Byte], price: Long) = {
  proveDlog(sellerPk) || sigmaProp(
    OUTPUTS(0).propositionBytes == sellerProp &&
    OUTPUTS(0).value >= price
  )
}
