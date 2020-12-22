## How simc does ilevel scaling

### First look

- Simc has an offline DB (`engine/dbc`) that stores all item data.
  E.g. see `engine/dbc/item_scaling.hpp` for definition, and
  `engine/dbc/generated/item_scaling.inc` for generated data.

- `engine/item/item.cpp` represents an item in the simc configuration
  language (e.g. `legs=,id=179351,bonus_id=6807/43/1498/6646`).

  It has various `item_t::decode_{stats,gems}` methods to parse the
  conf string into internal `.parsed` item data.

### Second look

- item_database::apply_item_bonus applies a item_bonus_entry_t onto a item_t.
  This handles "bonus_id=1502" (ilvl+30) and is a common code path. Let's take a
  deeper look...

- item_database::scaled_stat seems to be doing the core scaling part, based on
  a formula.

  1. Find the slot type (int of [0,3]) based on the subclass (weapon) or inventory_type (armor).
  2. Get random_prop_data_t from dbc.random_property(new_ilevel). This contains a 2-D table
     of (slot_type, item_quality) to item budget value.
  3. The stat can be calculated in two ways, either with a precise table lookup (3.1) or
     an approximation formula (3.2)

     3.1 This is when the original stat > 0 and budget value > 0:
         ```
         raw_stat = ceil(stat_alloc * budget / 10_000);
         // Or stamina.
         // cr_type is determined by item_database::item_combat_rating_type --
         // see combat_rating_multiplier_type.
         return dbc_t::combat_rating_multiplier(ilevel, cr_type) * raw_stat
         ```
         Which uses static tables `__combat_ratings_mult_by_ilvl` and `__stamina_mult_by_ilvl`
         (sc_scale_data.inc).

     3.1 Not sure if the approx formula is used or not... Probably not. It's simply
         15% stat per 15 ilevel.

- What is parsed_item_data_t::stat_alloc? This seems to be a normalized (ilevel / slot independent)
  stat value. It's calculated from stat_val (the original stat value):
  ```
  cr_type = item_database::item_combat_rating_type(inventory_type)
  cr_coeff = dbc_t::combat_rating_multiplier(original_ilevel, cr_type)
  stat_alloc = stat_val / cr_coeff * 10000.0 / budget
  ```
  cr_type is combat_rating_multiplier_type
  cr_coeff is read from static table __combat_ratings_mult_by_ilvl.

### Extra

- `SpellDataDump/bonus_ids.txt` shows the meaning of all bonus IDs. Very
  useful!

