#include <asm/bitops.h>

#define for_each_set_bit(bit, addr, size) \
        for ((bit) = find_first_bit((addr), (size));            \
             (bit) < (size);                                    \
             (bit) = find_next_bit((addr), (size), (bit) + 1))

/* same as for_each_set_bit() but use bit as value to start with */
#define for_each_set_bit_from(bit, addr, size) \
        for ((bit) = find_next_bit((addr), (size), (bit));      \
             (bit) < (size);                                    \
             (bit) = find_next_bit((addr), (size), (bit) + 1))

#define for_each_clear_bit(bit, addr, size) \
        for ((bit) = find_first_zero_bit((addr), (size));       \
             (bit) < (size);                                    \
             (bit) = find_next_zero_bit((addr), (size), (bit) + 1))

/* same as for_each_clear_bit() but use bit as value to start with */
#define for_each_clear_bit_from(bit, addr, size) \
        for ((bit) = find_next_zero_bit((addr), (size), (bit)); \
             (bit) < (size);                                    \
             (bit) = find_next_zero_bit((addr), (size), (bit) + 1))

/**
 * ror32 - rotate a 32-bit value right
 * @word: value to rotate
 * @shift: bits to roll
 */
static inline uint32_t ror32(uint32_t word, unsigned int shift)
{
        return (word >> shift) | (word << (32 - shift));
}

/**
 * find_next_bit - find the next set bit in a memory region
 * @addr: The address to base the search on
 * @offset: The bitnumber to start searching at
 * @size: The bitmap size in bits
 *
 * Returns the bit number for the next set bit
 * If no bits are set, returns @size.
 */
unsigned long find_next_bit(const unsigned long *addr, unsigned long size,
                            unsigned long offset);

/**
 * find_next_zero_bit - find the next cleared bit in a memory region
 * @addr: The address to base the search on
 * @offset: The bitnumber to start searching at
 * @size: The bitmap size in bits
 *
 * Returns the bit number of the next zero bit
 * If no bits are zero, returns @size.
 */
unsigned long find_next_zero_bit(const unsigned long *addr, unsigned long size,
                                 unsigned long offset);

/**
 * find_first_bit - find the first set bit in a memory region
 * @addr: The address to start the search at
 * @size: The maximum number of bits to search
 *
 * Returns the bit number of the first set bit.
 * If no bits are set, returns @size.
 */
unsigned long find_first_bit(const unsigned long *addr,
                             unsigned long size);

/**
 * find_first_zero_bit - find the first cleared bit in a memory region
 * @addr: The address to start the search at
 * @size: The maximum number of bits to search
 *
 * Returns the bit number of the first cleared bit.
 * If no bits are zero, returns @size.
 */
unsigned long find_first_zero_bit(const unsigned long *addr,
                                  unsigned long size);
