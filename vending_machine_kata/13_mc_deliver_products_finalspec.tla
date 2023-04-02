----------------- MODULE 13_mc_deliver_products_finalspec -----------------

EXTENDS 13_deliver_products_finalspec 

const_customer_names == {"c1"}
const_vending_machine_names == {"v1"}

const_min_coin_stock == 0
const_max_coin_stock == 5
const_min_product_stock == 1
const_max_product_stock == 3
const_products == [saffron_sky |-> 150, desert_white |-> 175, ocean_blue |-> 100]
const_cointypes == {25,50,100}
const_customer_cash == 250

\* no customer will ever own all products
invariant_product == 
            customers["c1"].assets.product["saffron_sky"] < 1
            \/
            customers["c1"].assets.product["ocean_blue"] < 1
            \/
            customers["c1"].assets.product["desert_white"] < 1
=============================================================================

