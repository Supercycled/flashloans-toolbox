// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

import "forge-std/Test.sol";

contract SharedSetupMainnet {
    address internal constant DAI = 0x6B175474E89094C44Da98b954EedeAC495271d0F;
    address internal constant USDC = 0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48;
    address internal constant WETH = 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2;
    address internal constant WBTC = 0x2260FAC5E5542a773Aa44fBCfeDf7C193bc2C599;
    address internal constant USDT = 0xdAC17F958D2ee523a2206206994597C13D831ec7;

    address internal constant wethProvider = 0x1C11BA15939E1C16eC7ca1678dF6160Ea2063Bc5;
    address internal constant daiProvider = 0xaD0135AF20fa82E106607257143d0060A7eB5cBf;
    address internal constant usdcProvider = 0x55FE002aefF02F77364de339a1292923A15844B8;
    address internal constant usdtProvider = 0xF977814e90dA44bFA03b6295A0616a897441aceC;
}

contract SharedSetupAvax{
    address internal constant DAI = 0xd586E7F844cEa2F87f50152665BCbc2C279D8d70;
    address internal constant USDC = 0xB97EF9Ef8734C71904D8002F8b6Bc66Dd9c48a6E;
    address internal constant WETH = 0x49D5c2BdFfac6CE2BFdB6640F4F80f226bc10bAB;
    address internal constant USDT = 0x9702230A8Ea53601f5cD2dc00fDBc13d4dF4A8c7;

    address internal constant daiProvider = 0x38dAE04E4c874AFC3d237E73677Aee43066aC1f2;
    address internal constant wethProvider = 0x334AD834Cd4481BB02d09615E7c11a00579A7909;
    address internal constant usdcProvider = 0x42d6Ce661bB2e5F5cc639E7BEFE74Ff9Fd649541;
    address internal constant usdtProvider = 0x4aeFa39caEAdD662aE31ab0CE7c8C2c9c0a013E8;
}

contract SharedSetupBsc{

    address WBNB = 0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c;
    address BUSD = 0xe9e7CEA3DedcA5984780Bafc599bD69ADd087D56;
    address CAKE = 0x0E09FaBB73Bd3Ade0a17ECC321fD13a19e81cE82;
    address USDT = 0x55d398326f99059fF775485246999027B3197955;
    address BTCB = 0x7130d2A12B9BCbFAe4f2634d864A1Ee1Ce3Ead9c;    

    address internal constant wbnbProvider = 0x59d779BED4dB1E734D3fDa3172d45bc3063eCD69;
    address internal constant busdProvider = 0x4B16c5dE96EB2117bBE5fd171E4d203624B014aa;
    address internal constant usdtProvider = 0x5a52E96BAcdaBb82fd05763E25335261B270Efcb;
    address internal constant btcbProvider = 0xF977814e90dA44bFA03b6295A0616a897441aceC;
}