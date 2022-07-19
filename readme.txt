FLASHLOANS TOOLBOX

Suite of smart contracts allowing easy flashLoans on UniswapV2, UniswapV3, AAVEV2 and AAVEV3. 
Make your contracts inherit one of those, call flashLoan() (AAVE) or flashSwap (Uni) and override the "onFlashLoan" functions with your own logic. 
Contains utils functions to estimate the max amount that can be flashloans as well as the fee that will be due. 

The test folder is usable with foundry. The sandard library is enough to test as all contracts have been flattened for simplicity. 
All tests are meant to be run on ETH mainnet fork except:

UniV2FlashSwap.t.sol: meant to be run on BSC mainnet fork
AaveV3FlashLoan.t.sol: meant to be run on AVAX mainnet fork

The test Hacker.t.sol show how you can use the BigFlashLoan contract on a Honeypot contract. 

List of contracts:

- UniV3FlashSwap: 

FlashSwap multiple assets accross multiple pools with the "flashSwap" function. 
Write your own logic in the "onUniV3FlashSwap" function. 
Repayment of the loan is automatic and managed by the "repayLoans" function. 
Override "initializeKnownPools" if you want to use more specific pools than the preset.
Fee differs according to the UNIV3 pool (0.1% -> 1%)

- UniV2FlashSwap: 

FlashSwap multiple assets accross multiple pairs with the "flashSwap" function. 
Write your own logic in the "onUniV2FlashSwap" function. 
Repayment of the loan is automatic and managed by the "repayLoans" function. 
Override "initializeKnownPools" if you want to use more specific pools than the preset.
Fee: 0,3%

- AaveV2FlashLoan:

FlashLoan multiple assets accross multiple reserves of the AAVE V2 protocol. 
Write your own logic in the "onAaveV2FlashLoan" function. 
Repayment of the loan is automatic and required ERC20 approvals done in the "executeOperation" function. 
Fee depends on the reserve. By default: 0.09% (could be less)


- AaveV3FlashLoan:

FlashLoan multiple assets accross multiple reserves of the AAVE V2 protocol. 
Write your own logic in the "onAaveV3FlashLoan" function. 
Repayment of the loan is automatic and required ERC20 approvals done in the "executeOperation" function. 
Fee depends on the reserve. By default: 0.09% (could be less)

- BigFlashLoan:

Designed for Ethereum mainnet. 
Combine the abilities of AaveV2FlashLoan and UniV3FlashSwap.
Use it if the reserves of AAVE V2 are not enough for your flashloan. 
Drain the liquidity of both AAVE V2 reserves and UNIV3 pools for multiple assets. 
Write your own logic in the "onflashLoan" function

contact: @_supercycled
