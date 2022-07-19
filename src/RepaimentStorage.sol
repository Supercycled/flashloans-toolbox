// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;
       
contract RepaimentStorage {

    // loans storage. Erased after each flashSwap call with repayLoans()
    mapping(address => Loan[]) loans; 
    mapping(address => uint256) totalBorrowPerToken;
    address[] public borrowedTokens; 

    struct Loan {
        address pool;
        address token;
        uint256 amount;
        uint256 fee;
    }

    // use this function if you want to du multiple flashloans
    function cleanupRepaimentStorage() internal {

        if (borrowedTokens.length > 0) {

            for (uint256 i = 0; i < borrowedTokens.length; i++) {

                address token = borrowedTokens[i];
                delete totalBorrowPerToken[token];
                delete loans[token];
            }
        }
        delete borrowedTokens;
    }
}

    
    
