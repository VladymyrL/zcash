// Copyright (c) 2016 Jack Grigg
// Copyright (c) 2016 The Zcash developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <algorithm>
#include <cassert>

template<size_t MAX_INDICES>
bool IsProbablyDuplicate(std::shared_ptr<eh_trunc> indices, size_t lenIndices)
{
    assert(lenIndices <= MAX_INDICES);
    bool checked_index[MAX_INDICES] = {false};
    int count_checked = 0;
    for (int z = 0; z < lenIndices; z++) {
        // Skip over indices we have already paired
        if (!checked_index[z]) {
            for (int y = z+1; y < lenIndices; y++) {
                if (!checked_index[y] && indices.get()[z] == indices.get()[y]) {
                    // Pair found
                    checked_index[y] = true;
                    count_checked += 2;
                    break;
                }
            }
        }
    }
    return count_checked == lenIndices;
}
