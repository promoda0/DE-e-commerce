"""
=====================================================================
 E-commerce Marketplace — OMS (Order Management System) Source Generator
=====================================================================
Simulates a ONE-TIME HISTORICAL EXTRACT from the OMS of an
Amazon/Flipkart-style Indian marketplace (3P sellers + some 1P).

Repo path : data_generator/generate_oms_orders.py
Run on    : Google Colab (writes to Google Drive) or locally.

Output layout (one folder per IST business date):
  <ROOT>/oms_export/2026-05-01/orders_20260501.csv        -> order header grain (1 row / order)
  <ROOT>/oms_export/2026-05-01/order_items_20260501.csv   -> order line grain (1 row / order line)
  <ROOT>/oms_export/2026-05-01/_manifest.json             -> row counts + control totals
  <ROOT>/master_seed/*.csv                                -> products / listings / sellers / customers
                                                             (future Catalog/CRM sources reuse these IDs)

Key source-system semantics (READ THIS — these are deliberate):
  * All timestamps are UTC (ISO-8601, 'Z'). Folders/files are by IST business date.
  * Status columns are "as of" EXTRACT_TS_IST (historical extract), not final truth.
  * Header money columns = amounts AT CHECKOUT. They are NOT adjusted for later
    item cancellations or returns. Item-level status tells what actually happened.
  * Item prices are GST-INCLUSIVE (Indian retail). tax_amount is INSIDE line_net_amount.
  * Money is computed in integer paise and written as rupees with 2 decimals.
  * Commission / seller settlement is NOT in OMS (belongs to Settlement system).
  * All personal data (names, phones, emails, addresses) is FAKE. Emails use example.com.

Determinism: same SEED -> same data. Each day uses its own RNG, so a single
day can be regenerated independently.
"""

import csv
import json
import math
import os
import random
import shutil
import time as _time
from bisect import bisect_left
from datetime import date, datetime, time, timedelta
from itertools import accumulate

# =====================================================================
# CONFIG — change only this block
# =====================================================================
SEED = 42
START_DATE = date(2026, 5, 1)
END_DATE = date(2026, 10, 31)                  # inclusive (184 days)
EXTRACT_TS_IST = datetime(2026, 11, 1, 6, 0)   # extract taken at this IST time

BASE_ORDERS_PER_DAY = 4500     # tuned for ~1 GB total; sample mode prints projection
NUM_CUSTOMERS = 250_000
NUM_PRODUCTS = 20_000
NUM_SELLERS = 1_500
NUM_1P_SELLERS = 15

MODE = "sample"                # "sample" -> first SAMPLE_DAYS only + size projection
SAMPLE_DAYS = 5                # "full"   -> all days

LOCAL_ROOT = "/content/ecom_source_data"                  # fast local disk in Colab
DRIVE_ROOT = "/content/drive/MyDrive/ecom_source_data"    # final destination
COPY_TO_DRIVE = True           # only used in "full" mode
# =====================================================================

IST_OFFSET = timedelta(hours=5, minutes=30)

# ---------------------------------------------------------------------
# Reference data
# ---------------------------------------------------------------------
# (city, state, zone, pincode_prefix, weight, is_metro)
CITIES = [
    ("Delhi", "Delhi", "NORTH", "110", 10, True),
    ("Gurugram", "Haryana", "NORTH", "122", 3, False),
    ("Noida", "Uttar Pradesh", "NORTH", "201", 3, False),
    ("Lucknow", "Uttar Pradesh", "NORTH", "226", 3, False),
    ("Jaipur", "Rajasthan", "NORTH", "302", 3, False),
    ("Chandigarh", "Chandigarh", "NORTH", "160", 2, False),
    ("Kanpur", "Uttar Pradesh", "NORTH", "208", 1.5, False),
    ("Ludhiana", "Punjab", "NORTH", "141", 1.5, False),
    ("Dehradun", "Uttarakhand", "NORTH", "248", 1, False),
    ("Mumbai", "Maharashtra", "WEST", "400", 10, True),
    ("Pune", "Maharashtra", "WEST", "411", 5, True),
    ("Ahmedabad", "Gujarat", "WEST", "380", 4, False),
    ("Surat", "Gujarat", "WEST", "395", 2.5, False),
    ("Nagpur", "Maharashtra", "WEST", "440", 1.5, False),
    ("Indore", "Madhya Pradesh", "WEST", "452", 2, False),
    ("Bhopal", "Madhya Pradesh", "WEST", "462", 1.5, False),
    ("Panaji", "Goa", "WEST", "403", 0.7, False),
    ("Bengaluru", "Karnataka", "SOUTH", "560", 10, True),
    ("Hyderabad", "Telangana", "SOUTH", "500", 7, True),
    ("Chennai", "Tamil Nadu", "SOUTH", "600", 6, True),
    ("Kochi", "Kerala", "SOUTH", "682", 2, False),
    ("Coimbatore", "Tamil Nadu", "SOUTH", "641", 1.5, False),
    ("Visakhapatnam", "Andhra Pradesh", "SOUTH", "530", 1.5, False),
    ("Mysuru", "Karnataka", "SOUTH", "570", 1, False),
    ("Thiruvananthapuram", "Kerala", "SOUTH", "695", 1, False),
    ("Kolkata", "West Bengal", "EAST", "700", 6, True),
    ("Bhubaneswar", "Odisha", "EAST", "751", 1.5, False),
    ("Patna", "Bihar", "EAST", "800", 2, False),
    ("Ranchi", "Jharkhand", "EAST", "834", 1, False),
    ("Guwahati", "Assam", "NORTHEAST", "781", 1.2, False),
    ("Shillong", "Meghalaya", "NORTHEAST", "793", 0.3, False),
    ("Imphal", "Manipur", "NORTHEAST", "795", 0.2, False),
]

# (fc_id, city, state, zone)
FULFILLMENT_CENTERS = [
    ("FC-DEL-01", "Gurugram", "Haryana", "NORTH"),
    ("FC-LKO-01", "Lucknow", "Uttar Pradesh", "NORTH"),
    ("FC-JAI-01", "Jaipur", "Rajasthan", "NORTH"),
    ("FC-BOM-01", "Bhiwandi", "Maharashtra", "WEST"),
    ("FC-PNQ-01", "Pune", "Maharashtra", "WEST"),
    ("FC-AMD-01", "Ahmedabad", "Gujarat", "WEST"),
    ("FC-BLR-01", "Bengaluru", "Karnataka", "SOUTH"),
    ("FC-HYD-01", "Hyderabad", "Telangana", "SOUTH"),
    ("FC-MAA-01", "Chennai", "Tamil Nadu", "SOUTH"),
    ("FC-CCU-01", "Kolkata", "West Bengal", "EAST"),
    ("FC-GAU-01", "Guwahati", "Assam", "NORTHEAST"),
]

# L1 -> line weight, (min_disc, max_disc), return_rate, return_window_days, qty_profile, code
CATEGORY_L1 = {
    "Electronics":     dict(w=15, disc=(0.05, 0.35), ret=0.06, win=7,  qty="single", code="ELC"),
    "Fashion":         dict(w=25, disc=(0.30, 0.70), ret=0.18, win=10, qty="normal", code="FSH"),
    "Home & Kitchen":  dict(w=15, disc=(0.10, 0.55), ret=0.05, win=7,  qty="normal", code="HMK"),
    "Beauty":          dict(w=12, disc=(0.05, 0.40), ret=0.03, win=7,  qty="normal", code="BTY"),
    "Grocery":         dict(w=15, disc=(0.00, 0.25), ret=0.00, win=0,  qty="bulk",   code="GRC"),
    "Books":           dict(w=6,  disc=(0.10, 0.40), ret=0.02, win=7,  qty="normal", code="BOK"),
    "Sports":          dict(w=6,  disc=(0.15, 0.50), ret=0.05, win=7,  qty="normal", code="SPT"),
    "Toys":            dict(w=6,  disc=(0.10, 0.50), ret=0.04, win=10, qty="normal", code="TOY"),
}

# L2 -> (L1, price_min, price_max, gst_rule, hsn, product nouns)
# gst_rule: int rate, or "APPAREL" (5% if unit price <= 2500 else 18%)  — simplified, not tax advice
CATEGORY_L2 = {
    "Mobiles":        ("Electronics", 7999, 89999, 18, "8517", ["5G Smartphone", "Smartphone"]),
    "Laptops":        ("Electronics", 29999, 149999, 18, "8471", ["Thin & Light Laptop", "Gaming Laptop"]),
    "Headphones":     ("Electronics", 499, 14999, 18, "8518", ["Wireless Earbuds", "Over-Ear Headphones", "Neckband"]),
    "Smartwatches":   ("Electronics", 1499, 29999, 18, "8517", ["Smartwatch", "Fitness Band"]),
    "Accessories":    ("Electronics", 199, 2499, 18, "8544", ["USB-C Cable", "Fast Charger", "Power Bank", "Phone Case"]),
    "Men Clothing":   ("Fashion", 399, 3999, "APPAREL", "6109", ["Cotton T-Shirt", "Slim Fit Jeans", "Casual Shirt", "Hoodie"]),
    "Women Clothing": ("Fashion", 449, 5999, "APPAREL", "6204", ["Kurta Set", "Maxi Dress", "Top", "Saree"]),
    "Footwear":       ("Fashion", 499, 6999, "APPAREL", "6403", ["Running Shoes", "Sneakers", "Sandals", "Formal Shoes"]),
    "Watches":        ("Fashion", 699, 12999, 18, "9102", ["Analog Watch", "Chronograph Watch"]),
    "Cookware":       ("Home & Kitchen", 299, 4999, 18, "7323", ["Non-Stick Kadai", "Pressure Cooker", "Tawa"]),
    "Furniture":      ("Home & Kitchen", 1999, 39999, 18, "9403", ["Study Table", "Office Chair", "Bookshelf"]),
    "Home Decor":     ("Home & Kitchen", 199, 2999, 18, "6302", ["Bedsheet Set", "Curtains", "Wall Clock"]),
    "Appliances":     ("Home & Kitchen", 1499, 49999, 18, "8516", ["Mixer Grinder", "Air Fryer", "Water Purifier"]),
    "Skincare":       ("Beauty", 199, 2499, 18, "3304", ["Face Serum", "Sunscreen SPF50", "Moisturizer"]),
    "Haircare":       ("Beauty", 149, 1499, 18, "3305", ["Shampoo", "Hair Oil", "Conditioner"]),
    "Fragrances":     ("Beauty", 299, 5999, 18, "3303", ["Eau de Parfum", "Body Mist"]),
    "Staples":        ("Grocery", 49, 1499, 5, "1006", ["Basmati Rice 5kg", "Atta 10kg", "Toor Dal 1kg"]),
    "Snacks":         ("Grocery", 20, 599, 5, "1905", ["Namkeen 400g", "Cookies Pack", "Dry Fruits 500g"]),
    "Beverages":      ("Grocery", 30, 799, 5, "2101", ["Green Tea 100 Bags", "Instant Coffee 200g"]),
    "Books":          ("Books", 99, 1499, 0, "4901", ["Paperback", "Hardcover"]),
    "Fitness":        ("Sports", 199, 14999, 18, "9506", ["Yoga Mat", "Dumbbell Set", "Treadmill"]),
    "Cricket":        ("Sports", 299, 9999, 18, "9506", ["English Willow Bat", "Cricket Kit"]),
    "Toys":           ("Toys", 199, 4999, 18, "9503", ["Building Blocks", "RC Car", "Board Game"]),
}

COLORS = ["Black", "White", "Blue", "Navy", "Grey", "Red", "Green", "Beige", "Silver", "Pink"]
SIZES = ["S", "M", "L", "XL", "XXL"]
FIRST_NAMES = ["Aarav", "Vivaan", "Aditya", "Arjun", "Sai", "Rohan", "Karan", "Rahul", "Amit", "Vikram",
               "Suresh", "Ravi", "Manoj", "Nikhil", "Pranav", "Ishaan", "Kabir", "Dev", "Harsh", "Yash",
               "Ananya", "Diya", "Priya", "Sneha", "Pooja", "Neha", "Kavya", "Riya", "Isha", "Meera",
               "Lakshmi", "Divya", "Anjali", "Shreya", "Aditi", "Nisha", "Swati", "Tanvi", "Fatima", "Sana",
               "Imran", "Arif", "Simran", "Gurpreet", "Joseph", "Mary", "Arun", "Deepa", "Gopal", "Bhavna"]
LAST_NAMES = ["Sharma", "Verma", "Gupta", "Singh", "Kumar", "Patel", "Shah", "Reddy", "Rao", "Nair",
              "Iyer", "Menon", "Das", "Banerjee", "Chatterjee", "Mukherjee", "Joshi", "Kulkarni", "Desai",
              "Mehta", "Agarwal", "Khan", "Sheikh", "Ansari", "Gill", "Sandhu", "Fernandes", "DSouza",
              "Pillai", "Yadav", "Mishra", "Tiwari", "Pandey", "Chauhan", "Rathore", "Bose", "Ghosh", "Naidu"]
STREETS = ["MG Road", "Station Road", "Park Street", "Ring Road", "Gandhi Nagar", "Nehru Colony",
           "Sector 15", "Sector 62", "Lake View Road", "Church Street", "Temple Road", "Civil Lines",
           "Model Town", "Indira Nagar", "Shastri Nagar", "Rajaji Street", "Market Road", "Hill View"]
LOCALITIES = ["Phase 1", "Phase 2", "Block A", "Block C", "East", "West", "Extension", "Layout", "Enclave"]

CHANNELS = (["ANDROID", "IOS", "MWEB", "WEB"], [55, 12, 18, 15])
PAYMENT_METHODS = (["UPI", "COD", "CREDIT_CARD", "DEBIT_CARD", "NETBANKING", "WALLET", "EMI", "PAY_LATER"],
                   [45, 22, 10, 8, 3, 4, 4, 4])
UTM_SOURCES = (["direct", "google", "facebook", "instagram", "email", "push_notification", "affiliate", ""],
               [40, 20, 8, 8, 5, 10, 5, 4])
HOUR_WEIGHTS = [1.0, 0.6, 0.35, 0.25, 0.2, 0.25, 0.5, 1.0, 1.6, 2.0, 2.3, 2.5,
                2.7, 2.6, 2.4, 2.3, 2.4, 2.6, 2.9, 3.3, 3.8, 4.2, 3.6, 2.2]
LINES_PER_ORDER = ([1, 2, 3, 4, 5, 6, 7, 8], [68, 20, 7, 3, 0.8, 0.6, 0.4, 0.2])

# (name, start, end, multiplier, campaign, electronics_boost)
SALE_EVENTS = [
    ("SUMMER_SALE_2026", date(2026, 5, 15), date(2026, 5, 18), 2.0, 1.3),
    ("FREEDOM_SALE_2026", date(2026, 8, 7), date(2026, 8, 11), 2.0, 1.4),
    ("BIG_FESTIVE_SALE_EARLY_ACCESS", date(2026, 9, 30), date(2026, 9, 30), 2.0, 1.6),
    ("BIG_FESTIVE_SALE_2026", date(2026, 10, 1), date(2026, 10, 7), 3.5, 1.8),
    ("DIWALI_SALE_2026", date(2026, 10, 20), date(2026, 10, 27), 2.0, 1.5),
]

CUSTOMER_CANCEL_REASONS = ["CHANGED_MIND", "FOUND_CHEAPER_ELSEWHERE", "DELIVERY_TOO_LATE",
                           "ORDERED_BY_MISTAKE", "ADDRESS_CHANGE_REQUIRED"]
SELLER_CANCEL_REASONS = ["SELLER_OUT_OF_STOCK", "SELLER_UNABLE_TO_SHIP"]
SYSTEM_CANCEL_REASONS = ["FRAUD_SUSPECTED", "PINCODE_NOT_SERVICEABLE"]
RTO_REASONS = ["CUSTOMER_REFUSED", "CUSTOMER_UNAVAILABLE", "ADDRESS_NOT_FOUND"]
RETURN_REASONS = {
    "Fashion": ["SIZE_ISSUE", "SIZE_ISSUE", "QUALITY_ISSUE", "NOT_AS_DESCRIBED", "CHANGED_MIND"],
    "_default": ["DEFECTIVE", "NOT_AS_DESCRIBED", "WRONG_ITEM_DELIVERED", "QUALITY_ISSUE", "CHANGED_MIND"],
}

ORDER_COLUMNS = [
    "order_id", "order_placed_at", "customer_id", "customer_email", "channel", "app_version",
    "is_plus_member", "order_status", "payment_method", "payment_status", "currency",
    "item_count", "total_units", "total_mrp", "item_subtotal", "product_discount",
    "coupon_code", "coupon_discount", "bank_offer_code", "bank_offer_discount",
    "shipping_fee", "cod_fee", "platform_fee", "gift_wrap_fee", "total_tax", "order_total",
    "delivery_type", "promised_delivery_date",
    "shipping_address_id", "shipping_name", "shipping_phone", "shipping_address_line1",
    "shipping_city", "shipping_state", "shipping_pincode", "shipping_zone",
    "is_gift", "utm_source", "utm_campaign",
    "confirmed_at", "shipped_at", "out_for_delivery_at", "delivered_at", "rto_at",
    "cancelled_at", "cancelled_by", "cancellation_reason", "updated_at",
]
ITEM_COLUMNS = [
    "order_item_id", "order_id", "line_number", "product_id", "listing_id", "seller_id", "seller_sku",
    "product_title", "brand", "category_l1", "category_l2", "hsn_code",
    "fulfillment_type", "fulfillment_center_id", "ship_from_state",
    "quantity", "unit_mrp", "unit_selling_price", "line_gross_amount", "allocated_order_discount",
    "line_net_amount", "gst_rate", "taxable_value", "tax_amount", "cgst_amount", "sgst_amount", "igst_amount",
    "item_status", "item_cancelled_at", "item_cancellation_reason",
    "is_returnable", "return_window_days", "return_requested_at", "return_received_at", "return_reason",
    "created_at", "updated_at",
]


# ---------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------
def rupees(paise):
    """integer paise -> '1234.50' string"""
    sign = "-" if paise < 0 else ""
    paise = abs(paise)
    return f"{sign}{paise // 100}.{paise % 100:02d}"


def utc(dt_ist):
    """naive IST datetime -> UTC ISO string"""
    return (dt_ist - IST_OFFSET).strftime("%Y-%m-%dT%H:%M:%SZ") if dt_ist else ""


def price_ending_9(value):
    """Indian retail style price: 1299, 499, 49"""
    v = int(round(value / 10.0)) * 10 - 1
    return max(9, v)


def round_div(num, den):
    """integer round-half-up division"""
    return (2 * num + den) // (2 * den)


def make_sampler(weights):
    cum = list(accumulate(weights))
    total = cum[-1]
    return cum, total


def sample(rng, items, cum_total):
    cum, total = cum_total
    return items[bisect_left(cum, rng.random() * total)]


def rand_alnum(rng, n):
    return "".join(rng.choice("ABCDEFGHJKLMNPQRSTUVWXYZ23456789") for _ in range(n))


def sale_for(d):
    for name, s, e, mult, boost in SALE_EVENTS:
        if s <= d <= e:
            return name, mult, boost, d == s
    return None, 1.0, 1.0, False


# ---------------------------------------------------------------------
# Master data (deterministic from SEED)
# ---------------------------------------------------------------------
def build_brands(rng):
    syl_a = ["Zen", "Kav", "Vol", "Nex", "Aur", "Tri", "Ved", "Lum", "Orb", "Sky", "Rio", "Tez", "Ark", "Nov", "Pix"]
    syl_b = ["ora", "tix", "ion", "ova", "ent", "ika", "aro", "yx", "ana", "ex", "ito", "era", "ux", "ani", "oz"]
    used, brands = set(), {}
    for l1 in CATEGORY_L1:
        lst = []
        while len(lst) < rng.randint(15, 30):
            b = rng.choice(syl_a) + rng.choice(syl_b)
            if b not in used:
                used.add(b)
                lst.append(b)
        brands[l1] = lst
    return brands


def build_sellers(rng):
    pre = ["Shree", "Om", "Royal", "Urban", "Prime", "Sai", "Metro", "Golden", "Bharat", "Star", "Lotus", "Apex"]
    suf = ["Traders", "Retail", "Enterprises", "Mart", "Distributors", "Store", "Ventures", "Collections"]
    city_cum = make_sampler([c[4] for c in CITIES])
    sellers = []
    for i in range(NUM_SELLERS):
        city = sample(rng, CITIES, city_cum)
        is_1p = i < NUM_1P_SELLERS
        sellers.append(dict(
            seller_id=f"SLR{100001 + i}",
            seller_name=(f"RetailNet {city[0]} Pvt Ltd" if is_1p else f"{rng.choice(pre)} {rng.choice(suf)}"),
            seller_type="1P" if is_1p else "3P",
            seller_city=city[0], seller_state=city[1], seller_zone=city[2],
            seller_rating=round(rng.uniform(3.2, 4.9), 1),
            onboarded_date=str(date(2019, 1, 1) + timedelta(days=rng.randint(0, 2600))),
        ))
    return sellers


def build_products(rng, brands, sellers):
    l2_names = list(CATEGORY_L2)
    l2_weights = []
    for l2 in l2_names:
        l1 = CATEGORY_L2[l2][0]
        n_same = sum(1 for x in CATEGORY_L2.values() if x[0] == l1)
        l2_weights.append(CATEGORY_L1[l1]["w"] / n_same)
    l2_cum = make_sampler(l2_weights)
    seller_cum = make_sampler([5.0 if s["seller_type"] == "1P" else rng.paretovariate(1.3) for s in sellers])

    products, listings = [], []
    for i in range(NUM_PRODUCTS):
        l2 = sample(rng, l2_names, l2_cum)
        l1, pmin, pmax, gst_rule, hsn, nouns = CATEGORY_L2[l2]
        meta = CATEGORY_L1[l1]
        brand = rng.choice(brands[l1])
        mrp = price_ending_9(math.exp(rng.uniform(math.log(pmin), math.log(pmax))))
        disc = rng.uniform(*meta["disc"])
        base_sp = min(mrp, price_ending_9(mrp * (1 - disc)))
        variant = rng.choice(SIZES) if l1 == "Fashion" and l2 != "Watches" else rng.choice(COLORS)
        model = f"{brand[:2].upper()}-{rng.randint(100, 999)}"
        title = f"{brand} {rng.choice(nouns)} {model} ({variant})"
        pid = meta["code"] + rand_alnum(rng, 13)
        product = dict(product_id=pid, product_title=title, brand=brand, category_l1=l1, category_l2=l2,
                       hsn_code=hsn, gst_rule=gst_rule, unit_mrp=mrp, listings=[])
        # 1-3 sellers per product (marketplace)
        chosen = set()
        for _ in range(rng.choice([1, 1, 1, 2, 2, 3])):
            s = sample(rng, sellers, seller_cum)
            if s["seller_id"] in chosen:
                continue
            chosen.add(s["seller_id"])
            sp = min(mrp, price_ending_9(base_sp * rng.uniform(0.97, 1.05)))
            platform_fulfilled = s["seller_type"] == "1P" or rng.random() < 0.55
            lst = dict(listing_id=f"LST{pid}{s['seller_id'][-3:]}", product_id=pid, seller_id=s["seller_id"],
                       seller_sku=f"{brand[:3].upper()}-{rng.randint(10000, 99999)}",
                       fulfillment_type="PLATFORM_FULFILLED" if platform_fulfilled else "SELLER_FULFILLED",
                       unit_selling_price=sp, seller=s)
            product["listings"].append(lst)
            listings.append(lst)
        products.append(product)
    return products, listings


def build_customers(rng):
    city_cum = make_sampler([c[4] for c in CITIES])
    customers = []
    for i in range(NUM_CUSTOMERS):
        fn, ln = rng.choice(FIRST_NAMES), rng.choice(LAST_NAMES)
        city = sample(rng, CITIES, city_cum)
        pin = city[3] + f"{rng.randint(1, 99):03d}"
        customers.append((
            f"CUS{100000000 + i}",                                    # 0 customer_id
            f"{fn} {ln}",                                             # 1 name
            str(rng.choice([6, 7, 8, 9])) + "".join(str(rng.randint(0, 9)) for _ in range(9)),  # 2 phone
            f"{fn}.{ln}{rng.randint(1, 9999)}@example.com".lower(),   # 3 email
            city,                                                     # 4 city tuple
            pin,                                                      # 5 pincode
            f"{rng.randint(1, 999)}, {rng.choice(STREETS)}, {rng.choice(LOCALITIES)}",  # 6 address
            rng.random() < 0.25,                                      # 7 is_plus_member
        ))
    # Pareto-like popularity: a minority of customers place most orders (repeat buyers)
    weights = [1.0 / ((r + 1) ** 0.75) for r in range(NUM_CUSTOMERS)]
    rng.shuffle(weights)
    return customers, make_sampler(weights)


def write_master_seed(root, sellers, products, listings, customers):
    out = os.path.join(root, "master_seed")
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "sellers.csv"), "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(sellers[0].keys()))
        w.writeheader()
        w.writerows(sellers)
    with open(os.path.join(out, "products.csv"), "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["product_id", "product_title", "brand", "category_l1", "category_l2", "hsn_code", "unit_mrp"])
        for p in products:
            w.writerow([p["product_id"], p["product_title"], p["brand"], p["category_l1"], p["category_l2"],
                        p["hsn_code"], rupees(p["unit_mrp"] * 100)])
    with open(os.path.join(out, "listings.csv"), "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["listing_id", "product_id", "seller_id", "seller_sku", "fulfillment_type", "unit_selling_price"])
        for l in listings:
            w.writerow([l["listing_id"], l["product_id"], l["seller_id"], l["seller_sku"],
                        l["fulfillment_type"], rupees(l["unit_selling_price"] * 100)])
    with open(os.path.join(out, "customers.csv"), "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["customer_id", "full_name", "phone", "email", "city", "state", "zone", "pincode",
                    "address_line1", "is_plus_member"])
        for c in customers:
            w.writerow([c[0], c[1], c[2], c[3], c[4][0], c[4][1], c[4][2], c[5], c[6], c[7]])


# ---------------------------------------------------------------------
# Order generation
# ---------------------------------------------------------------------
class Context:
    def __init__(self):
        rng = random.Random(SEED)
        self.brands = build_brands(rng)
        self.sellers = build_sellers(rng)
        self.products, self.listings = build_products(rng, self.brands, self.sellers)
        self.customers, self.cust_cum = build_customers(rng)

        # product popularity (Zipf within catalog) — some SKUs become best-sellers -> skew later
        self.by_l1 = {l1: [p for p in self.products if p["category_l1"] == l1] for l1 in CATEGORY_L1}
        self.l1_prod_cum = {}
        for l1, plist in self.by_l1.items():
            w = [1.0 / ((r + 1) ** 0.9) for r in range(len(plist))]
            rng.shuffle(w)
            # cheaper products sell more often (realistic AOV ~ ₹1.5-2.5K, not ₹10K)
            w = [wi * (p["unit_mrp"] ** -0.7) for wi, p in zip(w, plist)]
            self.l1_prod_cum[l1] = make_sampler(w)
        self.l1_names = list(CATEGORY_L1)
        self.fc_by_zone = {}
        for fc in FULFILLMENT_CENTERS:
            self.fc_by_zone.setdefault(fc[3], []).append(fc)
        self.hour_cum = make_sampler(HOUR_WEIGHTS)
        self.channel_cum = make_sampler(CHANNELS[1])
        self.pay_cum = make_sampler(PAYMENT_METHODS[1])
        self.utm_cum = make_sampler(UTM_SOURCES[1])
        self.lines_cum = make_sampler(LINES_PER_ORDER[1])


def gst_rate_for(gst_rule, unit_price_rupees):
    if gst_rule == "APPAREL":
        return 5 if unit_price_rupees <= 2500 else 18
    return gst_rule


def pick_quantity(rng, profile, unit_price):
    if profile == "single" or unit_price > 20000:
        return 1 if rng.random() < 0.97 else 2
    if profile == "bulk":
        return rng.choices([1, 2, 3, 4, 5, 6], [40, 25, 15, 10, 6, 4])[0]
    return rng.choices([1, 2, 3, 4], [85, 10, 4, 1])[0]


def delivery_days(rng, delivery_type, ship_zone, fc_zone, is_metro):
    if delivery_type == "SAME_DAY":
        return 0
    if delivery_type == "EXPRESS":
        return rng.choice([1, 1, 2])
    if ship_zone == "NORTHEAST":
        return rng.randint(6, 8)
    if ship_zone == fc_zone:
        return rng.randint(2, 3) if is_metro else rng.randint(3, 4)
    return rng.randint(4, 6)


def generate_day(ctx, d, out_dir):
    rng = random.Random(f"{SEED}-{d.isoformat()}")
    sale_name, mult, elec_boost, is_sale_first_day = sale_for(d)
    weekday_mult = 1.15 if d.weekday() >= 5 else 1.0
    salary_mult = 1.10 if d.day <= 5 else 1.0
    n_orders = int(BASE_ORDERS_PER_DAY * mult * weekday_mult * salary_mult * rng.uniform(0.92, 1.08))

    l1_weights = [CATEGORY_L1[l1]["w"] * (elec_boost if l1 == "Electronics" else 1.0) for l1 in ctx.l1_names]
    l1_cum = make_sampler(l1_weights)
    hour_weights = list(HOUR_WEIGHTS)
    if is_sale_first_day:
        hour_weights[0] *= 6  # midnight rush when sale goes live
    hour_cum = make_sampler(hour_weights)
    app_idx = (d - START_DATE).days // 14
    yymmdd = d.strftime("%y%m%d")
    platform_fee_paise = 500 if d >= date(2026, 8, 1) else 0   # business introduced ₹5 platform fee on 1-Aug

    os.makedirs(out_dir, exist_ok=True)
    f_orders = open(os.path.join(out_dir, f"orders_{d:%Y%m%d}.csv"), "w", newline="", encoding="utf-8")
    f_items = open(os.path.join(out_dir, f"order_items_{d:%Y%m%d}.csv"), "w", newline="", encoding="utf-8")
    wo, wi = csv.writer(f_orders), csv.writer(f_items)
    wo.writerow(ORDER_COLUMNS)
    wi.writerow(ITEM_COLUMNS)

    ctl = dict(orders=0, items=0, sum_order_total=0, sum_line_net=0)

    for seq in range(1, n_orders + 1):
        cust = sample(rng, ctx.customers, ctx.cust_cum)
        cid, cname, cphone, cemail, city, pin, addr, is_plus = cust
        addr_id = f"ADR{cid[3:]}A"
        if rng.random() < 0.10:  # alternate (office) address in same city
            addr = f"{rng.randint(1, 999)}, {rng.choice(STREETS)}, {rng.choice(LOCALITIES)}"
            pin = city[3] + f"{rng.randint(1, 99):03d}"
            addr_id = f"ADR{cid[3:]}B"
        city_name, state, zone, _, _, is_metro = city

        hour = sample(rng, list(range(24)), hour_cum)
        placed = datetime.combine(d, time(hour, rng.randint(0, 59), rng.randint(0, 59)))
        channel = sample(rng, CHANNELS[0], ctx.channel_cum)
        app_version = (f"{9 + app_idx // 6}.{app_idx % 6}.{rng.randint(0, 3)}"
                       if channel in ("ANDROID", "IOS") else "")
        order_id = f"OD{yymmdd}{seq:07d}{rng.randint(0, 99999):05d}"

        # ---------- lines ----------
        n_lines = sample(rng, LINES_PER_ORDER[0], ctx.lines_cum)
        first_l1 = sample(rng, ctx.l1_names, l1_cum)
        lines, used_pids = [], set()
        for _ in range(n_lines * 2):  # attempts (skip duplicate products)
            if len(lines) == n_lines:
                break
            l1 = first_l1 if (not lines or rng.random() < 0.5) else sample(rng, ctx.l1_names, l1_cum)
            prod = sample(rng, ctx.by_l1[l1], ctx.l1_prod_cum[l1])
            if prod["product_id"] in used_pids:
                continue
            used_pids.add(prod["product_id"])
            lst = rng.choice(prod["listings"])
            sp = lst["unit_selling_price"]
            if sale_name:
                sp = max(9, min(sp, price_ending_9(sp * (1 - rng.uniform(0.0, 0.15)))))
            qty = pick_quantity(rng, CATEGORY_L1[l1]["qty"], sp)
            lines.append(dict(prod=prod, lst=lst, sp=sp, qty=qty))

        total_mrp = sum(ln["prod"]["unit_mrp"] * ln["qty"] for ln in lines) * 100
        subtotal = sum(ln["sp"] * ln["qty"] for ln in lines) * 100

        # ---------- payment ----------
        pay = sample(rng, PAYMENT_METHODS[0], ctx.pay_cum)
        if pay == "EMI" and subtotal < 300000:
            pay = "CREDIT_CARD"
        if pay == "COD" and subtotal > 5000000:
            pay = "UPI"

        # ---------- discounts ----------
        coupon_code, coupon = "", 0
        if rng.random() < (0.25 if sale_name else 0.12):
            options = []
            if subtotal >= 49900:
                options.append(("SAVE10", min(subtotal // 10, 15000)))
            if subtotal >= 99900:
                options.append(("FLAT100", 10000))
            if subtotal >= 249900:
                options.append(("FLAT250", 25000))
            if sale_name and subtotal >= 99900:
                options.append(("FEST20", min(subtotal // 5, 50000)))
            if options:
                coupon_code, coupon = rng.choice(options)
        bank_code, bank = "", 0
        if pay in ("CREDIT_CARD", "DEBIT_CARD", "EMI") and subtotal >= 299900 and \
                rng.random() < (0.70 if sale_name else 0.35):
            bank_code = "CARD10"
            bank = min(subtotal // 10, 150000 if sale_name else 100000)
        order_disc = min(coupon + bank, subtotal - 100)

        # allocate order-level discount to lines proportionally (paise, remainder on last line)
        allocated = 0
        for idx, ln in enumerate(lines):
            gross = ln["sp"] * ln["qty"] * 100
            ln["gross"] = gross
            a = order_disc - allocated if idx == len(lines) - 1 else order_disc * gross // subtotal
            ln["alloc"] = a
            allocated += a
            ln["net"] = gross - a

        # ---------- fees ----------
        r = rng.random()
        if is_metro and r < 0.06:
            delivery_type = "SAME_DAY"
        elif r < 0.18:
            delivery_type = "EXPRESS"
        else:
            delivery_type = "STANDARD"
        if is_plus:
            shipping_fee = 0
        elif delivery_type == "SAME_DAY":
            shipping_fee = 9900
        elif delivery_type == "EXPRESS":
            shipping_fee = 7000
        else:
            shipping_fee = 0 if subtotal >= 49900 else 4000
        cod_fee = 1000 if pay == "COD" else 0
        is_gift = rng.random() < 0.04
        gift_fee = 3000 if is_gift else 0
        order_total = subtotal - order_disc + shipping_fee + cod_fee + platform_fee_paise + gift_fee

        # ---------- fulfillment & tax per line ----------
        total_tax = 0
        main_fc_zone = zone
        for ln in lines:
            s = ln["lst"]["seller"]
            if ln["lst"]["fulfillment_type"] == "PLATFORM_FULFILLED":
                fcs = ctx.fc_by_zone.get(zone) if rng.random() < 0.75 else None
                fc = rng.choice(fcs) if fcs else rng.choice(FULFILLMENT_CENTERS)
                ln["fc_id"], ln["from_state"], ln["from_zone"] = fc[0], fc[2], fc[3]
            else:
                ln["fc_id"], ln["from_state"], ln["from_zone"] = "", s["seller_state"], s["seller_zone"]
            rate = gst_rate_for(ln["prod"]["gst_rule"], ln["sp"])
            taxable = round_div(ln["net"] * 100, 100 + rate)
            tax = ln["net"] - taxable
            if ln["from_state"] == state:
                cg = tax // 2
                ln["tax"] = (rate, taxable, tax, cg, tax - cg, 0)
            else:
                ln["tax"] = (rate, taxable, tax, 0, 0, tax)
            total_tax += tax
        main_fc_zone = lines[0]["from_zone"]

        # ---------- lifecycle (final truth, then cut at extract time) ----------
        promise_days = delivery_days(rng, delivery_type, zone, main_fc_zone, is_metro)
        promised_date = d + timedelta(days=promise_days)
        confirmed = placed + timedelta(minutes=rng.randint(1, 15))
        if delivery_type == "SAME_DAY":
            shipped = placed + timedelta(hours=rng.uniform(1.5, 4))
            delivered = shipped + timedelta(hours=rng.uniform(2, 6))
        else:
            shipped = placed + timedelta(hours=rng.uniform(8, 40) if delivery_type == "STANDARD"
                                         else rng.uniform(4, 16))
            target = datetime.combine(promised_date, time(rng.randint(9, 20), rng.randint(0, 59)))
            delivered = max(target, shipped + timedelta(hours=6))
        if rng.random() < 0.08:  # late delivery (breached promise)
            delivered += timedelta(days=rng.randint(1, 4))
        ofd = delivered - timedelta(hours=rng.uniform(2, 7))

        events = [("PLACED", placed)]
        cancelled_at = cancel_by = cancel_reason = None
        rto_at = None
        r = rng.random()
        if pay != "COD" and r < 0.02:
            outcome = "PAYMENT_FAILED"
            cancelled_at = placed + timedelta(minutes=rng.randint(2, 20))
            cancel_by, cancel_reason = "SYSTEM", "PAYMENT_FAILED"
            events.append(("PAYMENT_FAILED", cancelled_at))
        else:
            events.append(("CONFIRMED", confirmed))
            r2 = rng.random()
            rto_p = 0.06 if pay == "COD" else 0.015
            if r2 < 0.07:
                outcome = "CANCELLED"
                cancelled_at = confirmed + (shipped - confirmed) * rng.random()
                cb = rng.choices(["CUSTOMER", "SELLER", "SYSTEM"], [70, 20, 10])[0]
                cancel_by = cb
                cancel_reason = rng.choice({"CUSTOMER": CUSTOMER_CANCEL_REASONS,
                                            "SELLER": SELLER_CANCEL_REASONS,
                                            "SYSTEM": SYSTEM_CANCEL_REASONS}[cb])
                events.append(("CANCELLED", cancelled_at))
            elif r2 < 0.07 + rto_p:
                outcome = "RTO"
                rto_at = ofd + timedelta(days=rng.uniform(1, 4))
                cancel_reason = rng.choice(RTO_REASONS)
                cancel_by = "LOGISTICS"
                events += [("SHIPPED", shipped), ("OUT_FOR_DELIVERY", ofd), ("RTO", rto_at)]
            else:
                outcome = "DELIVERED"
                events += [("SHIPPED", shipped), ("OUT_FOR_DELIVERY", ofd), ("DELIVERED", delivered)]

        visible = [e for e in events if e[1] <= EXTRACT_TS_IST]
        order_status = visible[-1][0]
        ev = {name: ts for name, ts in visible}
        hdr_cancelled_at = ev.get("CANCELLED") or ev.get("PAYMENT_FAILED")
        show_cancel = hdr_cancelled_at is not None or "RTO" in ev
        last_ts = visible[-1][1]

        # ---------- item status ----------
        partial_cancel_idx = None
        if outcome in ("DELIVERED", "RTO") and len(lines) > 1 and rng.random() < 0.04:
            partial_cancel_idx = rng.randrange(len(lines))
        item_rows = []
        n_returned = n_cancelled_items = 0
        for idx, ln in enumerate(lines):
            prod = ln["prod"]
            l1 = prod["category_l1"]
            meta = CATEGORY_L1[l1]
            returnable = meta["win"] > 0
            istatus = order_status
            i_cancel_at = i_cancel_reason = ""
            ret_req = ret_rcv = ret_reason = ""
            i_updated = last_ts
            if order_status in ("CANCELLED", "PAYMENT_FAILED"):
                i_cancel_at, i_cancel_reason = utc(hdr_cancelled_at), cancel_reason
            if idx == partial_cancel_idx:
                t = confirmed + (shipped - confirmed) * rng.random()
                if t <= EXTRACT_TS_IST:
                    istatus, i_cancel_at, i_cancel_reason = "CANCELLED", utc(t), "SELLER_OUT_OF_STOCK"
                    i_updated = t
                    n_cancelled_items += 1
            elif order_status == "DELIVERED" and returnable and rng.random() < meta["ret"]:
                req = delivered + timedelta(days=rng.uniform(0.3, meta["win"]))
                rcv = req + timedelta(days=rng.uniform(2, 7))
                if req <= EXTRACT_TS_IST:
                    ret_req = utc(req)
                    ret_reason = rng.choice(RETURN_REASONS.get(l1, RETURN_REASONS["_default"]))
                    istatus, i_updated = "RETURN_REQUESTED", req
                    if rcv <= EXTRACT_TS_IST:
                        ret_rcv, istatus, i_updated = utc(rcv), "RETURNED", rcv
                        n_returned += 1
            rate, taxable, tax, cg, sg, ig = ln["tax"]
            item_rows.append([
                f"OI{yymmdd}{seq:07d}{idx + 1:02d}", order_id, idx + 1,
                prod["product_id"], ln["lst"]["listing_id"], ln["lst"]["seller_id"], ln["lst"]["seller_sku"],
                prod["product_title"], prod["brand"], l1, prod["category_l2"], prod["hsn_code"],
                ln["lst"]["fulfillment_type"], ln["fc_id"], ln["from_state"],
                ln["qty"], rupees(prod["unit_mrp"] * 100), rupees(ln["sp"] * 100),
                rupees(ln["gross"]), rupees(ln["alloc"]), rupees(ln["net"]),
                rate, rupees(taxable), rupees(tax), rupees(cg), rupees(sg), rupees(ig),
                istatus, i_cancel_at, i_cancel_reason,
                returnable, meta["win"], ret_req, ret_rcv, ret_reason,
                utc(placed), utc(max(i_updated, last_ts)),
            ])
            ctl["sum_line_net"] += ln["net"]

        # ---------- payment status (mirror of payment system, as of extract) ----------
        n_lines_done = n_returned + n_cancelled_items
        if order_status == "PAYMENT_FAILED":
            pay_status = "FAILED"
        elif pay == "COD":
            if order_status == "CANCELLED":
                pay_status = "NOT_APPLICABLE"
            elif order_status == "RTO":
                pay_status = "NOT_COLLECTED"
            elif order_status == "DELIVERED":
                pay_status = "PARTIALLY_REFUNDED" if n_returned else "COLLECTED"
            else:
                pay_status = "PENDING"
        else:
            if order_status in ("CANCELLED", "RTO"):
                pay_status = "REFUNDED"
            elif n_lines_done == len(lines):
                pay_status = "REFUNDED"
            elif n_lines_done:
                pay_status = "PARTIALLY_REFUNDED"
            else:
                pay_status = "CAPTURED"

        utm_src = sample(rng, UTM_SOURCES[0], ctx.utm_cum)
        utm_campaign = sale_name if (sale_name and utm_src) else ("always_on" if utm_src not in ("", "direct") else "")
        updated_at = max([last_ts] + [datetime.strptime(r_[-1], "%Y-%m-%dT%H:%M:%SZ") + IST_OFFSET
                                      for r_ in item_rows])

        wo.writerow([
            order_id, utc(placed), cid, cemail, channel, app_version,
            is_plus, order_status, pay, pay_status, "INR",
            len(lines), sum(ln["qty"] for ln in lines), rupees(total_mrp), rupees(subtotal),
            rupees(total_mrp - subtotal), coupon_code, rupees(coupon), bank_code, rupees(bank),
            rupees(shipping_fee), rupees(cod_fee), rupees(platform_fee_paise), rupees(gift_fee),
            rupees(total_tax), rupees(order_total),
            delivery_type, promised_date.isoformat(),
            addr_id, cname, cphone, addr, city_name, state, pin, zone,
            is_gift, utm_src, utm_campaign,
            utc(ev.get("CONFIRMED")), utc(ev.get("SHIPPED")), utc(ev.get("OUT_FOR_DELIVERY")),
            utc(ev.get("DELIVERED")), utc(ev.get("RTO")),
            utc(hdr_cancelled_at), cancel_by if show_cancel else "", cancel_reason if show_cancel else "",
            utc(updated_at),
        ])
        wi.writerows(item_rows)
        ctl["orders"] += 1
        ctl["items"] += len(item_rows)
        ctl["sum_order_total"] += order_total

    f_orders.close()
    f_items.close()
    manifest = {
        "source_system": "OMS",
        "business_date": d.isoformat(),
        "extract_ts_utc": utc(EXTRACT_TS_IST),
        "files": {
            f"orders_{d:%Y%m%d}.csv": {"row_count": ctl["orders"], "sum_order_total": rupees(ctl["sum_order_total"])},
            f"order_items_{d:%Y%m%d}.csv": {"row_count": ctl["items"], "sum_line_net_amount": rupees(ctl["sum_line_net"])},
        },
    }
    with open(os.path.join(out_dir, "_manifest.json"), "w") as f:
        json.dump(manifest, f, indent=2)
    return ctl


def dir_size(path):
    total = 0
    for root, _, files in os.walk(path):
        for fn in files:
            total += os.path.getsize(os.path.join(root, fn))
    return total


def main():
    t0 = _time.time()
    if os.path.exists(LOCAL_ROOT):
        shutil.rmtree(LOCAL_ROOT)
    os.makedirs(LOCAL_ROOT)

    print("Building master data ...")
    ctx = Context()
    write_master_seed(LOCAL_ROOT, ctx.sellers, ctx.products, ctx.listings, ctx.customers)

    all_days = [START_DATE + timedelta(days=i) for i in range((END_DATE - START_DATE).days + 1)]
    days = all_days[:SAMPLE_DAYS] if MODE == "sample" else all_days
    totals = dict(orders=0, items=0)
    for i, d in enumerate(days, 1):
        ctl = generate_day(ctx, d, os.path.join(LOCAL_ROOT, "oms_export", d.isoformat()))
        totals["orders"] += ctl["orders"]
        totals["items"] += ctl["items"]
        if i % 10 == 0 or i == len(days):
            print(f"  {d}  day {i}/{len(days)}  orders so far={totals['orders']:,}  "
                  f"elapsed={_time.time() - t0:,.0f}s")

    export_bytes = dir_size(os.path.join(LOCAL_ROOT, "oms_export"))
    print(f"\nOrders={totals['orders']:,}  Items={totals['items']:,}  "
          f"oms_export size={export_bytes / 1e6:,.1f} MB")

    if MODE == "sample":
        # project using multipliers of all days vs sample days
        def day_factor(d):
            _, m, _, _ = sale_for(d)
            return m * (1.15 if d.weekday() >= 5 else 1.0) * (1.10 if d.day <= 5 else 1.0)
        proj = export_bytes * sum(day_factor(d) for d in all_days) / sum(day_factor(d) for d in days)
        print(f"Projected FULL size ≈ {proj / 1e9:.2f} GB  "
              f"(adjust BASE_ORDERS_PER_DAY if far from 1 GB, then set MODE='full')")
        return

    if COPY_TO_DRIVE:
        try:
            from google.colab import drive  # noqa
            drive.mount("/content/drive")
        except ImportError:
            print("Not on Colab -> skipping Drive copy")
            return
        print(f"Copying to {DRIVE_ROOT} ... (few minutes)")
        shutil.copytree(LOCAL_ROOT, DRIVE_ROOT, dirs_exist_ok=True)
        print(f"Done. Drive size = {dir_size(DRIVE_ROOT) / 1e9:.2f} GB")
    print(f"Total time {_time.time() - t0:,.0f}s")


if __name__ == "__main__":
    main()
