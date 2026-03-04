# Expensive Expressions and Functions

This document catalogs expressions and functions that are computationally expensive
and are good candidates for optimization techniques like hoisting above LIMIT operators,
pushing below aggregations, or other query rewriting strategies.

## Categories

### 1. Serialization/Deserialization Functions

These functions convert between different data formats and representations.

#### Protobuf Conversions
- `pb_to_json` - Convert protobuf to JSON
- `json_to_pb` - Convert JSON to protobuf

#### JSON/JSONB Conversions
- `to_json` - Convert arbitrary types to JSON
- `to_jsonb` - Convert arbitrary types to JSONB
- `row_to_json` - Convert row to JSON object
- `array_to_json` - Convert array to JSON array
- `json_populate_record` - Populate record from JSON
- `jsonb_populate_record` - Populate record from JSONB
- `json_to_record` - Convert JSON to record type
- `jsonb_to_record` - Convert JSONB to record type
- `json_to_recordset` - Convert JSON array to recordset
- `jsonb_to_recordset` - Convert JSONB array to recordset

#### Binary/Text Encoding
- `encode` - Encode binary data (hex, base64, escape)
- `decode` - Decode binary data
- `convert_from` - Convert from encoding to text
- `convert_to` - Convert text to encoding

#### XML Functions
- `xmlparse` - Parse XML text
- `xmlserialize` - Serialize XML to text
- `xpath` - XML path navigation
- `xpath_exists` - Check XML path existence
- `table_to_xml` - Convert table to XML
- `query_to_xml` - Convert query result to XML
- `cursor_to_xml` - Convert cursor to XML

### 2. Aggregate Functions

These accumulate data across multiple rows.

#### String/Array Aggregates
- `string_agg` - Concatenate strings with separator
- `array_agg` - Aggregate values into array
- `json_agg` - Aggregate values into JSON array
- `jsonb_agg` - Aggregate values into JSONB array
- `json_object_agg` - Aggregate key-value pairs into JSON object
- `jsonb_object_agg` - Aggregate key-value pairs into JSONB object

#### Statistical Aggregates (expensive for large datasets)
- `percentile_cont` - Continuous percentile
- `percentile_disc` - Discrete percentile
- `mode` - Most frequent value
- `regr_*` - Regression functions (regr_slope, regr_intercept, etc.)
- `corr` - Correlation coefficient
- `covar_pop`, `covar_samp` - Covariance

### 3. JSON/JSONB Operations

These manipulate JSON data structures.

#### Construction
- `json_build_object` - Build JSON object from variadic arguments
- `jsonb_build_object` - Build JSONB object from variadic arguments
- `json_build_array` - Build JSON array from variadic arguments
- `jsonb_build_array` - Build JSONB array from variadic arguments
- `json_object` - Build JSON object from arrays
- `jsonb_object` - Build JSONB object from arrays

#### Manipulation
- `jsonb_set` - Set value in JSONB at path
- `jsonb_insert` - Insert value into JSONB
- `jsonb_set_lax` - Set value with null handling
- `json_strip_nulls` - Remove null values
- `jsonb_strip_nulls` - Remove null values from JSONB

#### Path/Traversal Operations
- `json_extract_path` - Extract value at path
- `jsonb_extract_path` - Extract value at path (JSONB)
- `json_extract_path_text` - Extract text at path
- `jsonb_extract_path_text` - Extract text at path (JSONB)
- `json_array_elements` - Expand JSON array to rows
- `jsonb_array_elements` - Expand JSONB array to rows
- `json_array_elements_text` - Expand array to text rows
- `jsonb_array_elements_text` - Expand array to text rows
- `json_each` - Expand object to key-value rows
- `jsonb_each` - Expand object to key-value rows
- `json_each_text` - Expand object to text key-value rows
- `jsonb_each_text` - Expand object to text key-value rows
- `json_object_keys` - Get object keys
- `jsonb_object_keys` - Get object keys
- `json_populate_recordset` - Expand JSON array to recordset
- `jsonb_populate_recordset` - Expand JSONB array to recordset

### 4. String Operations

Especially expensive on large strings or with complex patterns.

#### Regular Expressions
- `regexp_replace` - Replace using regex
- `regexp_split_to_array` - Split string by regex into array
- `regexp_split_to_table` - Split string by regex into table
- `regexp_matches` - Match regex and return captures
- `regexp_match` - First match of regex
- `regexp_count` - Count regex matches (PG 15+)

#### String Manipulation
- `concat_ws` - Concatenate with separator (expensive with many args)
- `string_to_array` - Split string into array
- `array_to_string` - Join array into string
- `repeat` - Repeat string (expensive for large counts)
- `overlay` - Replace substring
- `translate` - Character-by-character translation
- `replace` - Replace all occurrences
- `split_part` - Split and extract part
- `string_to_table` - Split string into rows

#### Case Conversion (on large strings)
- `upper`, `lower`, `initcap` - (cheap on small strings, expensive on large)

### 5. Cryptographic and Hash Functions

These are computationally intensive by design.

#### Hash Functions
- `md5` - MD5 hash
- `sha1` - SHA-1 hash
- `sha224` - SHA-224 hash
- `sha256` - SHA-256 hash
- `sha384` - SHA-384 hash
- `sha512` - SHA-512 hash

#### Encryption/Decryption
- `encrypt` - Symmetric encryption
- `decrypt` - Symmetric decryption
- `encrypt_iv` - Encryption with IV
- `decrypt_iv` - Decryption with IV
- `pgp_sym_encrypt` - PGP symmetric encryption
- `pgp_sym_decrypt` - PGP symmetric decryption
- `pgp_pub_encrypt` - PGP public key encryption
- `pgp_pub_decrypt` - PGP public key decryption
- `armor`, `dearmor` - ASCII armor encoding/decoding
- `pgp_key_id` - Extract PGP key ID

#### Random Generation
- `gen_random_uuid` - Generate random UUID
- `gen_random_bytes` - Generate random bytes

### 6. Geospatial Functions

Operations on geometric and geographic data.

#### Format Conversions
- `ST_AsGeoJSON` - Convert to GeoJSON
- `ST_AsText` - Convert to WKT (Well-Known Text)
- `ST_AsEWKT` - Convert to EWKT (Extended WKT)
- `ST_AsBinary` - Convert to WKB (Well-Known Binary)
- `ST_AsEWKB` - Convert to EWKB
- `ST_AsKML` - Convert to KML
- `ST_AsGML` - Convert to GML
- `ST_AsSVG` - Convert to SVG
- `ST_GeomFromGeoJSON` - Parse GeoJSON
- `ST_GeomFromText` - Parse WKT
- `ST_GeomFromEWKT` - Parse EWKT
- `ST_GeomFromWKB` - Parse WKB
- `ST_GeomFromEWKB` - Parse EWKB

#### Spatial Analysis
- `ST_Buffer` - Create buffer around geometry
- `ST_Intersection` - Compute intersection
- `ST_Union` - Compute union
- `ST_Difference` - Compute difference
- `ST_SymDifference` - Compute symmetric difference
- `ST_ConvexHull` - Compute convex hull
- `ST_Simplify` - Simplify geometry
- `ST_SimplifyPreserveTopology` - Topology-preserving simplification
- `ST_Centroid` - Compute centroid
- `ST_PointOnSurface` - Find point on surface
- `ST_Distance` - Calculate distance
- `ST_Area` - Calculate area
- `ST_Length` - Calculate length
- `ST_Perimeter` - Calculate perimeter

#### Spatial Relationships (expensive on complex geometries)
- `ST_Contains` - Test containment
- `ST_Within` - Test if within
- `ST_Covers` - Test if covers
- `ST_CoveredBy` - Test if covered by
- `ST_Crosses` - Test if crosses
- `ST_Overlaps` - Test if overlaps
- `ST_Touches` - Test if touches
- `ST_Intersects` - Test if intersects
- `ST_Relate` - Compute DE-9IM relationship

### 7. Set-Returning Functions (SRFs)

Functions that return multiple rows.

#### Generators
- `generate_series` - Generate series of values (expensive for large ranges)
- `generate_subscripts` - Generate array subscripts
- `unnest` - Expand array to rows (expensive for large arrays)

#### JSON/JSONB SRFs
- See JSON section above for array_elements, each, etc.

### 8. Window Functions

While not always expensive, some window functions can be costly.

#### Ranking Functions
- `row_number()` - Assign row numbers
- `rank()` - Assign ranks with gaps
- `dense_rank()` - Assign ranks without gaps
- `percent_rank()` - Relative rank
- `cume_dist()` - Cumulative distribution
- `ntile(n)` - Divide into buckets

#### Offset Functions
- `lag()` - Access previous row
- `lead()` - Access next row
- `first_value()` - First value in window
- `last_value()` - Last value in window
- `nth_value()` - Nth value in window

### 9. Date/Time Functions

#### Parsing and Formatting
- `to_char` - Format to string (expensive with complex format strings)
- `to_timestamp` - Parse timestamp from string
- `to_date` - Parse date from string
- `parse_timestamp` - Parse with format string
- `parse_date` - Parse date with format string
- `parse_time` - Parse time with format string
- `parse_interval` - Parse interval

#### Timezone Operations
- `timezone` - Convert timezone (requires lookup)
- `at time zone` - Timezone conversion operator

### 10. Subqueries

#### Scalar Subqueries
- Any scalar subquery in SELECT list (especially correlated)
- Example: `SELECT (SELECT max(x) FROM t2 WHERE t2.id = t1.id) FROM t1`

#### Correlated Subqueries
- Subqueries that reference outer query columns
- Must be evaluated once per outer row

#### EXISTS/NOT EXISTS
- Can be expensive if not optimized to semi-join/anti-join

### 11. User-Defined Functions (UDFs)

#### Characteristics that make UDFs expensive:
- `VOLATILE` volatility - must execute per row
- `STABLE` volatility - must execute per statement
- Complex PL/pgSQL logic
- Functions that call other expensive functions
- Functions without `LEAKPROOF` annotation
- Functions that perform I/O or external calls

### 12. Array Operations

#### Array Construction
- `array[...]` - Array literal (expensive with many elements)
- `ARRAY(subquery)` - Array from subquery

#### Array Functions
- `array_cat` - Concatenate arrays
- `array_append` - Append to array
- `array_prepend` - Prepend to array
- `array_remove` - Remove element from array
- `array_replace` - Replace elements in array
- `array_position` - Find position in array (linear search)
- `array_positions` - Find all positions in array

### 13. Full-Text Search

#### Text Search Functions
- `to_tsvector` - Convert text to tsvector
- `to_tsquery` - Parse text search query
- `plainto_tsquery` - Plain text to query
- `phraseto_tsquery` - Phrase to query
- `websearch_to_tsquery` - Web search to query
- `ts_headline` - Generate highlighted headline
- `ts_rank` - Rank by relevance
- `ts_rank_cd` - Rank by cover density

### 14. Miscellaneous Expensive Operations

#### Type Conversions
- Complex type casts (e.g., geometry to JSON)
- Array to text conversions
- Record to JSON conversions

#### String Similarity
- `similarity` - Trigram similarity
- `levenshtein` - Edit distance
- `soundex` - Soundex encoding
- `metaphone` - Metaphone encoding

#### Network Functions
- `inet_merge` - Merge networks
- `inet_same_family` - Check same family
- Network calculations on large ranges

## Heuristics for Identifying Expensive Expressions

### Property-Based Detection
1. **Volatility**: `VOLATILE` > `STABLE` > `IMMUTABLE`
2. **Class**: Aggregate functions are expensive per group
3. **Set-returning**: SRFs are expensive per row
4. **I/O**: Functions that touch disk/network

### Pattern-Based Detection
1. Functions operating on large/unbounded data (arrays, strings, JSON)
2. Functions with nested loops or recursive operations
3. Functions involving parsing or format conversion
4. Cryptographic operations (intentionally slow)

### Cost Estimation Factors
- Input size (string length, array size, JSON depth)
- Number of iterations (regex matches, series generations)
- Algorithmic complexity (O(n²) string operations)
- External dependencies (timezone databases, dictionaries)

## Usage in Optimization Rules

These functions are good candidates for:

1. **Hoisting above LIMIT**: Don't compute expensive expressions for rows that will be discarded
2. **Pushing below aggregations**: Compute once per group instead of for all rows
3. **Memoization**: Cache results when possible (for STABLE/IMMUTABLE)
4. **Projection pushdown**: Don't compute if result isn't needed
5. **Common subexpression elimination**: Avoid redundant computation

## Examples

### Good: Hoist above LIMIT
```sql
-- Before optimization
SELECT expensive_func(col) FROM table LIMIT 10;

-- After: Only compute for 10 rows
SELECT expensive_func(col) FROM (SELECT col FROM table LIMIT 10);
```

### Good: Push computation after filtering
```sql
-- Before
SELECT expensive_func(col) FROM table WHERE id = 5;

-- After: Filter first, then compute (if only 1 row matches)
SELECT expensive_func(col) FROM (SELECT col FROM table WHERE id = 5);
```

### Important: Volatile function semantics

Volatile functions **CAN** be hoisted, reordered, duplicated, or eliminated:

```sql
-- CAN hoist volatile functions above LIMIT
SELECT gen_random_uuid() FROM table LIMIT 10;
-- Can be optimized to only generate 10 UUIDs

-- CAN eliminate unused volatile expressions
SELECT x FROM (SELECT nextval(seq), x FROM xy);
-- Can eliminate nextval() call

-- CAN duplicate during predicate pushdown
SELECT * FROM xy INNER JOIN xz ON xy.x=xz.x WHERE xy.x=random();
-- Can push random() to both sides
```

The optimizer only guarantees:
1. CASE/IF branches evaluated conditionally (unless leakproof)
2. Volatile expressions not treated as constants (e.g., can't eliminate ORDER BY random())
3. CTEs with volatile operators evaluated exactly once

See pkg/sql/opt/props/volatility.go for details.

## Notes

- This list focuses on PostgreSQL/CockroachDB built-in functions
- Actual cost depends on input size and system resources
- Some "expensive" functions are cheap with small inputs
- Always verify with benchmarks before optimizing
- UDFs should be analyzed based on their implementation
