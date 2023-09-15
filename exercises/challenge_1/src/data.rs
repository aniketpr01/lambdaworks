use lambdaworks_math::unsigned_integer::u64_utils::element::UnsignedInteger;

use crate::field::ChallengeElement;

pub fn pairs() -> [(ChallengeElement, ChallengeElement); 10] {
    [
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                183240637262039384,
                10134058328874369520,
                15648036570429036245,
                12373630818091389922,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                58125280520191997,
                7563295584845025545,
                10505934299123791696,
                7243434167283202274,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                53793503318333808,
                3207637959751464466,
                14494950274942836597,
                4136788124041118761,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                311364612610444531,
                15966843845133580520,
                11733134576879619546,
                15728250733723614304,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                568211605542321808,
                3665906368153986805,
                17170247225323812746,
                15915536692872977361,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                217852115983473995,
                4166846794769956288,
                6317771942840139764,
                14625875306968385082,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                207549010898490221,
                4243616016599017025,
                9848596493685366018,
                7918147356679190828,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                477451920176997361,
                15490207318061191317,
                18290929028207201553,
                12313619366283486653,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                373838775372616312,
                2673582186589028492,
                7759321698787748238,
                13844063650817543069,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                501628185314588506,
                360101150955423272,
                9640428090924426801,
                4582961170966616797,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                87489608385277507,
                7831811476568950391,
                2088690257692214216,
                5066699409404733431,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                355875529635643805,
                13282387072996050664,
                8345773773609640016,
                16439847079178157230,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                81907762606414085,
                13685489810001955596,
                1500287613219709574,
                2446883281376595718,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                285826094074462510,
                2412521888121343816,
                17074562155301273597,
                743918196287760338,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                539334648243077342,
                1241819602239411681,
                5927184179348544209,
                11640860157447976251,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                502287359473451983,
                2105484562428168146,
                2070489610481465832,
                9074849931098206603,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                536884484895507488,
                5347777065114328110,
                18395674441153693721,
                10552627961256589724,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                55173036628470166,
                605478499650837527,
                3313559020999214570,
                17867174237670907305,
            ])),
        ),
        (
            ChallengeElement::new(UnsignedInteger::from_limbs([
                420067545220093896,
                2975148993333630768,
                15772310561964876975,
                5736425213799489626,
            ])),
            ChallengeElement::new(UnsignedInteger::from_limbs([
                245745081194512045,
                17128497290282674116,
                12860542778099276299,
                11433466637600805681,
            ])),
        ),
    ]
}
