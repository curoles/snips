/**@file
 * @brief     Custom string allocation
 * @author    Igor Lesik 2017
 * @copyright Igor Lesik 2017
 *
 *
 *
 */
#include "string.h"

#include <assert.h>
#include <string.h>
#include <stdio.h>

#include "alloc.h"

char* string(char* s)
{
#if (0)
    char* terminal;

    for (terminal = s; *terminal/*!='\0'*/; terminal++) {;}

    return stringL(s, /*len=*/s - terminal);
#endif
    return stringL(s, strlen(s));
}

typedef struct String String;

struct String {
    char* str;     ///< allocated C string
    uint len;      ///< length of the string
    String* link;  ///< next allocated string in a list/bucket
};

// hash table
static String* g_buckets[SZ_1K] = {NULL,};

static
char* install_new_string(char* str, uint len, String* p, uint bucket_id)
{
    static char* g_next = NULL;
    static char* g_strlimit = NULL;

    if (g_next + len + 1 >= g_strlimit) {
        uint alloc_block_size = len + 4*SZ_1K;
        g_next = allocate(alloc_block_size, ALLOC_ARENA_PERM);
        g_strlimit = g_next + alloc_block_size;
    }

    NEW(p, ALLOC_ARENA_PERM);
    p->str = g_next;
    p->len = len;
    p->link = g_buckets[bucket_id]; // insert at front of the list

    //for (int i = 0; i < len; i++) { g_next[i] = str[i]; }
    strncpy(g_next, str, len);
    g_next[len] = 0;

    g_next = g_next + len + 1;

    g_buckets[bucket_id] = p; // set head of the list to p

    return p->str;
}

// Rotating hash
// http://burtleburtle.net/bob/hash/doobs.html
static
uint hash(char* key, uint len)
{
    uint hash = len;

    for (int i = 0; i < len; i++) {
        hash = (hash<<4)^(hash>>28)^key[i];
    }

    hash &= sizeof_array(g_buckets) - 1; // size MUST be 2^N for this to work!!!

    assert(0 <= hash && hash < sizeof_array(g_buckets));

    return hash;
}

/** Store input string in permanently allocated memory space. 
 *  @param s input string
 *  @param len lenght of input string, \0 included
 *  @return pointer to permanently stored copy of input string
 */
char* stringL(char* str, uint len)
{
    uint bucket_id = hash(str, len);

    String* p = NULL;

    // Check if the string is already allocated.
    // Go through the list and compare one by one.
    for (p = g_buckets[bucket_id]; p; p = p->link) {
        if (len == p->len) {
            if (strncmp(str, p->str, len) == 0) {
                return p->str;
            }
        }
    }

    // Could not find the string inside allocated, create new allocation.
    assert(p == NULL);

    char* alloc_str = install_new_string(str, len, p, bucket_id);

    assert(alloc_str != NULL);

    return alloc_str;
}

char* string_append(const char* str1, const char* str2)
{
    char buf[1024];
    size_t len = snprintf(buf, sizeof(buf), "%s%s", str1, str2);

    assert(sizeof(buf) > len);

    return stringL(buf, len);
}


char* stringd(int value)
{
    char buf[32];
    
    size_t len = snprintf(buf, sizeof(buf), "%d", value);
    assert(len < sizeof(buf));

    return stringL(buf, len + 1);
}

static
uint get_bucket_list_size(uint bucket_id)
{
    String* item = g_buckets[bucket_id];

    uint list_len = 0;
    while (item != NULL) {
        list_len++;
        item = item->link;
    }

    return list_len;
}

#if (0)
#include <stdlib.h>
static
char* rand_string(char* str, size_t size)
{
    static const char charset[] =
        "12345678abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_+-)(*<>?!@#$%";

    if (size) {
        --size;
        for (size_t n = 0; n < size; n++) {
            int key = rand() % (int) (sizeof charset - 1);
            str[n] = charset[key];
        }
        str[size] = '\0';
    }

    return str;
}
#endif

void show_string_hash_distribution(uint chunk)
{
    enum {NUM_BUCKETS = sizeof_array(g_buckets), NORM_SZ = 100};
    uint dist[NUM_BUCKETS] = {0,};
    uint max_len = 1;

    /*char buf[256]; for (int i = 0; i < 100000; i++) {
        string(rand_string(buf,sizeof(buf)));
    }*/

    for (uint bucket_id = 0; bucket_id < NUM_BUCKETS; bucket_id++) {
        uint list_len = get_bucket_list_size(bucket_id);
        max_len = (list_len > max_len)? list_len:max_len;
        dist[bucket_id] = list_len;
    }

    chunk = chunk? :1;

    for (uint bucket_id = 0; bucket_id < NUM_BUCKETS; bucket_id++) {
        uint val = 0;
        for (uint i = 0; i < chunk && bucket_id < NUM_BUCKETS; i++) {
            val += dist[bucket_id];
            bucket_id++;
        }
        bucket_id--;

        uint norm = (val * NORM_SZ) / (max_len * chunk);
        fprintf(stdout, "%4u %4u %0*u\n", bucket_id, val, norm, norm);
    }

}
