/* file hash.h 
 * 13/1/98 introduced new parallel structure gen_hash_table for `gen' type
 * 2/1/96 introduced new parallel structure char_hash_table, for hashing
 * character strings.
 * 23.12.94. Changed storage method to having separate blocks, to avoid
 * having to copy large chunks of data.
 * 24/10/94.
 */

typedef struct {
  boolean fixed_len; /* true if the records have fixed length */
  int rec_len;       /* the length of the records - used when fixed_len true */
  int num_blocks;    /* The number of blocks or data - initially 1 */
  int **table_block;   /* for the records themselves - table_block[i] (i>=0)
			* points to start of (i+1)-th block of records.
			*/
  int **table_data_ptr;  /* table_data_ptr[i] points to the address
                          * in table_data where the i-th record begins.
                          * For space reasons, this is only used when
                          * fixed_len is false - for fixed_len true, it can
                          * be calculated. The length of the record is
			  * calculated by using table_data_ptr[i+1].
			  * (except when record i+1 starts a new block)
                          */
  int *current_ptr;  /* The location in table_data where the current
                      * record for investigation begins.
                      */
  int num_recs;      /* The current number of records. */
  int maxrecs;       /* the largest number of records allowed + 1
                      * - can be increased dynamically if exceeded.
                      */
  int num_recs_inc;  /* The initial value of num_recs, and the increment
                      * when it is increased.
                      */
  int block_space;   /* space occupied in current block */
  int tot_space;     /* total space occupied in all blocks */
  int space_inc;     /* The initial value of allocated space for records,
		      * and the increment when it is increased -
		      * the size of each block of data
                      */
  int recs_per_block; /* When fixed_len true, the number of recs in each block
			* equal to (maxspace/rec_len).
			*/
  int modulus;       /* used as modulus when calculating hash values */
  int hash_values;   /* the maximum number of hash_values -
                      * modulus*hash_values*2 must not exceed MAXINT.
                      */
  int *first_rec;    /* first_rec[i] (for 0 <= i < hash_values)
                      * is the number of the first record with hashed value i.
                      */
  int *next_rec;     /* next_rec[i] is the number of a record with the same
                      * hashed value as record number i -
                      * or -1, if there are no further such records.
                      * note that next_rec requires space maxrecs.
                      */
  int *block_start_rec; /* block_start_rec[i] is the number of the record which
			 * starts at table_block[i] - only needed when fixed_len
			 * is false.
			 */
  int *block_last_len; /* The length of the last record in table_block[i].
                       * only needed when fixed_len is false.
		       */

/* NOTE: Record numbering starts at 0, and record number 0 is always the
 * record in which all entries are 0.
 * For variable length records, this will have length 0.
 */
} hash_table;

typedef struct {
  boolean fixed_len; /* true if the records have fixed length */
  int rec_len;       /* the length of the records - used when fixed_len true */
  int num_blocks;    /* The number of blocks or data - initially 1 */
  unsigned short **table_block;
                       /* for the records themselves - table_block[i] (i>=0)
			* points to start of (i+1)-th block of records.
			*/
  unsigned short **table_data_ptr;
			 /* table_data_ptr[i] points to the address
                          * in table_data where the i-th record begins.
                          * For space reasons, this is only used when
                          * fixed_len is false - for fixed_len true, it can
                          * be calculated. The length of the record is
			  * calculated by using table_data_ptr[i+1].
			  * (except when record i+1 starts a new block)
                          */
  unsigned short *current_ptr;
		     /* The location in table_data where the current
                      * record for investigation begins.
                      */
  int num_recs;      /* The current number of records. */
  int maxrecs;       /* the largest number of records allowed + 1
                      * - can be increased dynamically if exceeded.
                      */
  int num_recs_inc;  /* The initial value of num_recs, and the increment
                      * when it is increased.
                      */
  int block_space;   /* space occupied in current block */
  int tot_space;     /* total space occupied in all blocks */
  int space_inc;     /* The initial value of allocated space for records,
		      * and the increment when it is increased -
		      * the size of each block of data
                      */
  int recs_per_block; /* When fixed_len true, the number of recs in each block
			* equal to (maxspace/rec_len).
			*/
  int modulus;       /* used as modulus when calculating hash values */
  int hash_values;   /* the maximum number of hash_values -
                      * modulus*hash_values*2 must not exceed MAXINT.
                      */
  int *first_rec;    /* first_rec[i] (for 0 <= i < hash_values)
                      * is the number of the first record with hashed value i.
                      */
  int *next_rec;     /* next_rec[i] is the number of a record with the same
                      * hashed value as record number i -
                      * or -1, if there are no further such records.
                      * note that next_rec requires space maxrecs.
                      */
  int *block_start_rec; /* block_start_rec[i] is the number of the record which
			 * starts at table_block[i] - only needed when fixed_len
			 * is false.
			 */
  int *block_last_len; /* The length of the last record in table_block[i].
                       * only needed when fixed_len is false.
		       */

/* NOTE: Record numbering starts at 0, and record number 0 is always the
 * record in which all entries are 0.
 * For variable length records, this will have length 0.
 */
} short_hash_table;

typedef struct {
  boolean fixed_len; /* true if the records have fixed length */
  int rec_len;       /* the length of the records - used when fixed_len true */
  int num_blocks;    /* The number of blocks or data - initially 1 */
  char **table_block;
                       /* for the records themselves - table_block[i] (i>=0)
			* points to start of (i+1)-th block of records.
			*/
  char **table_data_ptr;
			 /* table_data_ptr[i] points to the address
                          * in table_data where the i-th record begins.
                          * For space reasons, this is only used when
                          * fixed_len is false - for fixed_len true, it can
                          * be calculated. The length of the record is
			  * calculated by using table_data_ptr[i+1].
			  * (except when record i+1 starts a new block)
                          */
  char *current_ptr;
		     /* The location in table_data where the current
                      * record for investigation begins.
                      */
  int num_recs;      /* The current number of records. */
  int maxrecs;       /* the largest number of records allowed + 1
                      * - can be increased dynamically if exceeded.
                      */
  int num_recs_inc;  /* The initial value of num_recs, and the increment
                      * when it is increased.
                      */
  int block_space;   /* space occupied in current block */
  int tot_space;     /* total space occupied in all blocks */
  int space_inc;     /* The initial value of allocated space for records,
		      * and the increment when it is increased -
		      * the size of each block of data
                      */
  int recs_per_block; /* When fixed_len true, the number of recs in each block
			* equal to (maxspace/rec_len).
			*/
  int modulus;       /* used as modulus when calculating hash values */
  int hash_values;   /* the maximum number of hash_values -
                      * modulus*hash_values*2 must not exceed MAXINT.
                      */
  int *first_rec;    /* first_rec[i] (for 0 <= i < hash_values)
                      * is the number of the first record with hashed value i.
                      */
  int *next_rec;     /* next_rec[i] is the number of a record with the same
                      * hashed value as record number i -
                      * or -1, if there are no further such records.
                      * note that next_rec requires space maxrecs.
                      */
  int *block_start_rec; /* block_start_rec[i] is the number of the record which
			 * starts at table_block[i] - only needed when fixed_len
			 * is false.
			 */
  int *block_last_len; /* The length of the last record in table_block[i].
                       * only needed when fixed_len is false.
		       */

/* NOTE: Record numbering starts at 0, and record number 0 is always the
 * record in which all entries are 0.
 * For variable length records, this will have length 0.
 */
} char_hash_table;

typedef struct {
  boolean fixed_len; /* true if the records have fixed length */
  int rec_len;       /* the length of the records - used when fixed_len true */
  int num_blocks;    /* The number of blocks or data - initially 1 */
  gen **table_block;
                       /* for the records themselves - table_block[i] (i>=0)
			* points to start of (i+1)-th block of records.
			*/
  gen **table_data_ptr;
			 /* table_data_ptr[i] points to the address
                          * in table_data where the i-th record begins.
                          * For space reasons, this is only used when
                          * fixed_len is false - for fixed_len true, it can
                          * be calculated. The length of the record is
			  * calculated by using table_data_ptr[i+1].
			  * (except when record i+1 starts a new block)
                          */
  gen *current_ptr;
		     /* The location in table_data where the current
                      * record for investigation begins.
                      */
  int num_recs;      /* The current number of records. */
  int maxrecs;       /* the largest number of records allowed + 1
                      * - can be increased dynamically if exceeded.
                      */
  int num_recs_inc;  /* The initial value of num_recs, and the increment
                      * when it is increased.
                      */
  int block_space;   /* space occupied in current block */
  int tot_space;     /* total space occupied in all blocks */
  int space_inc;     /* The initial value of allocated space for records,
		      * and the increment when it is increased -
		      * the size of each block of data
                      */
  int recs_per_block; /* When fixed_len true, the number of recs in each block
			* equal to (maxspace/rec_len).
			*/
  int modulus;       /* used as modulus when calculating hash values */
  int hash_values;   /* the maximum number of hash_values -
                      * modulus*hash_values*2 must not exceed MAXINT.
                      */
  int *first_rec;    /* first_rec[i] (for 0 <= i < hash_values)
                      * is the number of the first record with hashed value i.
                      */
  int *next_rec;     /* next_rec[i] is the number of a record with the same
                      * hashed value as record number i -
                      * or -1, if there are no further such records.
                      * note that next_rec requires space maxrecs.
                      */
  int *block_start_rec; /* block_start_rec[i] is the number of the record which
			 * starts at table_block[i] - only needed when fixed_len
			 * is false.
			 */
  int *block_last_len; /* The length of the last record in table_block[i].
                       * only needed when fixed_len is false.
		       */

/* NOTE: Record numbering starts at 0, and record number 0 is always the
 * record in which all entries are 0.
 * For variable length records, this will have length 0.
 */
} gen_hash_table;
