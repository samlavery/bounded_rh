
/-! ###### certificate data `SixW15ST`: 4827 cells, 4361 leaves (axis-coded walk) (half-space) ###### -/

namespace Zeta23Ext.Bridge.ThreePoint.SixW15STData

open Zeta23Ext.Bridge.ThreePoint Zeta23Ext.Bridge.ThreePoint.SixW15ST

set_option maxRecDepth 100000
local notation "N" => CTN.node
local notation "E" => CTN.nil

def cover0 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 39936, false),
  (39936, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 57344, true),
  (57344, 57856, true),
  (57856, 401408, false)]

theorem cover0_ok : SixW15ST.coverCheck 25326800 (SC / 2) 401408 cover0 = true := by decide +kernel

def cover1 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 60416, true),
  (60416, 74240, false),
  (74240, 74496, true),
  (74496, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 88832, true),
  (88832, 88960, true),
  (88960, 89088, true),
  (89088, 237568, false)]

theorem cover1_ok : SixW15ST.coverCheck 48244400 (SC / 2) 237568 cover1 = true := by decide +kernel

def cover2 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 37888, false),
  (37888, 38016, true),
  (38016, 38144, true),
  (38144, 38400, true),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 60416, true),
  (60416, 73728, false),
  (73728, 73984, true),
  (73984, 74240, true),
  (74240, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 89088, true),
  (89088, 89344, true),
  (89344, 89600, true),
  (89600, 221184, false)]

theorem cover2_ok : SixW15ST.coverCheck 52857300 (SC / 2) 221184 cover2 = true := by decide +kernel

def cover3 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 31744, true),
  (31744, 38400, false),
  (38400, 38912, true),
  (38912, 40960, true),
  (40960, 49152, true),
  (49152, 57344, true),
  (57344, 59392, true),
  (59392, 60416, true),
  (60416, 74240, false),
  (74240, 74496, true),
  (74496, 74752, true),
  (74752, 75776, true),
  (75776, 77824, true),
  (77824, 81920, true),
  (81920, 86016, true),
  (86016, 88064, true),
  (88064, 88576, true),
  (88576, 88832, true),
  (88832, 88960, true),
  (88960, 89088, true),
  (89088, 237568, false)]

theorem cover3_ok : SixW15ST.coverCheck 48244400 (SC / 2) 237568 cover3 = true := by decide +kernel

def cover4 : List (ℕ × ℕ × Bool) := [
  (16384, 24576, true),
  (24576, 28672, true),
  (28672, 30720, true),
  (30720, 39936, false),
  (39936, 40448, true),
  (40448, 40960, true),
  (40960, 43008, true),
  (43008, 45056, true),
  (45056, 49152, true),
  (49152, 53248, true),
  (53248, 55296, true),
  (55296, 57344, true),
  (57344, 57856, true),
  (57856, 401408, false)]

theorem cover4_ok : SixW15ST.coverCheck 25326800 (SC / 2) 401408 cover4 = true := by decide +kernel

def bits : ℕ := 38324836944313246766091436396630837201915054226680653300835015805441822383817333520178489359827695454839772978735924589941963562276175924578564251565445521111897510243378840188517096284262206995653188923381143223546469681198864974625475583370083739215669990377065247683770138337986242005370116810656914417927827261936165575184015493500811488032777960066730985380324659305970926495057533311279562056737819915317902889677626025433273744872014817850861476073249025374922010581140059839773155730775786193532230836130201340258594891526969876577308382702547128447002250400548631995937050093384455311243433118610151276863295771372304307740042352603758593519179166105142156211167154671499806219113064778460920298573450333066703562494444800760030267301478172180867011714307279401599457461704360724929564015346304336732864844583352413807896102452045837497188328356798369420637468647052453912951560438291089411518978798974106598936820157531116724868454045124505928591758913073517138561691946690955717884702144407097643814220053928219859450007097100439089568007725981175511271142197348338252773393834215195315519943190438164247078171574628266591524636869734021147311535260623340546265120360674758251043779567355137193513396637332235761007893229946099136336715130279005586387980599021016019888919588107605674517904654932070323039304562760973232157673581742293872770553926494069139953657369492545273398786041785593657725099624939174506539987979667176101112746999695800714265998170105018732919947174940056812899342070592805591823163795158987274559633809087859840196232543919668756586860915215480335505346247298998927384065558946778680150053506857511253419898785855968144908467241301357724107472163330557598421349543845847446812712684857309008190081783370805649228053241142742309162304682223134745500426537108466543883662174091860557949905808886131155863461473955254145740505762252666331814353756456258913748821207592431385214229196487120509942577139155645941565730350839956718934052593312018135726867310775312393703471863055527150663518121149203818707398286969439731968557152641523130790738110663775738526459706312636209178654613527902349141426197013520212475124252262975980021527947660951866500876246073771123320701059850042450983494550496413283822279088580555905713238829987908488672601355526201650703308054716156412301055881337543083800683486399892530036062034946884847965571069471131264711790184829134570435045697898030861892529792396603923502968123802620644995712520745964899369842429654676023438320304143833322208915847984732426290183336274218123994690177588532504823020131267482590532172700408298287177276849145677080682353254183063697514735887252341378148848509930621395982854639389573830544479691678806684375647163677398453512820775765333812247654404275918049831475288529130348884305377511695030331444445786601330217454942526987572242803791514506037406155382105820960958432371436180831785271582786330196830077897404413086417998219084495787425926605141503155201966528884298451782197321905515744668583476628446379595958931540564567443321756433329072082675582116819275973412895159209726341425429302229792020660337868118184281886596229336065143830926021444036687346617881953885079086078218599622484711611174967530821650321388108371836862208624163717478058098484750340450386579799006631786512112419489844077629231767560863811430375328241746364409355768242999940970666886305328398855792070092641115405667497226434458381330460307950276439008805176902799025072991923679813124114947635308551295738698649108311323305609289015674252693828554856938162981796950134381309167759116840032248954016542826116149227337969370491847861142489224507637919983255357291468329943728461641953805429249364965546575379897316646769800716558116293726464000561185185381910024885455055982550102665997320221623749799568283807652305741224113099462195720462280233075341273933544415859951483589931356546439965625350157250733693017213579505547587890155848158291386984274453490561727632221214081209507320581875100834558808851443682284501990312416129975770061168167358558754306205417465056791649715227743577054868915304928281079034510448790645335263032377800907689413070506115796053920716895935362389977219561603894291290758308896986093298817563892461609935211103550679586320075710245901443324278319288939044435842800067399350196547506552841701014217637312304401607265744409796601987931096683947640979560439068182891717953377006584718914510953406658977263011777837125951450101320525823619003353859376212627644677057828285892464173293043461801402427997673855236920265745572026831691746081359400040691670566565202133803796702510162919262949136888208119253312819093271476439014074825156051613891233131330420822576924540893103640460543683383097434584580959599690185260772113819751130222958360165184707261356345307229354337080524459732254870789618409658392489892690992744543977273193223917954762972465836872009774062637280629652564502464269012102194573396062599729993495013391469331554224304593401061661664464667811280967977592614524770143965863981557387867330044399613146790363886545245673508222549660635524413087996874707395857028384775834673508859907835351622405105737616508862162397635076738736461457342724396870795254773908529469156702798122952023604989675187297972628530444051517991490468756457212895418323264873779081458007484714288638078357296650512066190405297448786600749533001254422688756282246528680819378366732389903833830953018147687371865555652997032656010706543551484884438460529010432562365729262958791645484376695959706042320910170194097161516983635058314541595643818899799858996094790419635819016496268467898317614106682633424631550772813106544384643468455188638286797198435495322647554941617998754854791649349632588339140917314922872687653694770721372201788675364195811188964836159581397149991015138183826372197410425158660075386752981710611731232751308874317203575412140848938836235787840704814671639476128643729117315467112957298532685715766316681898275922164021081482310189247647094506547084286937753539367416838623330825176208849312222317906771218656408901037016092989657097201635078280293880656904596513750184818190159725723061426188478094797689332520223742071632925827118451759194599753922788568659619123365082230770888633147829293408838077975110136901603603969101961178153088206603001515974101593146952265815043614051828514593812783156614238549289671588909762772012628038064080778287908107013960367434841848339255948115530829325610105136482473943313

noncomputable def bx0 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 30720 39936)

theorem wk0 : SixW15ST.walk bits 64 0 bx0 = some 721 := by decide +kernel

noncomputable def bx1 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 31744 37888 31744 38400 57856 401408)

theorem wk1 : SixW15ST.walk bits 64 721 bx1 = some 2527 := by decide +kernel

noncomputable def bx2 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 30720 39936)

theorem wk2 : SixW15ST.walk bits 64 2527 bx2 = some 3658 := by decide +kernel

noncomputable def bx3 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 31744 37888 60416 74240 57856 401408)

theorem wk3 : SixW15ST.walk bits 64 3658 bx3 = some 4944 := by decide +kernel

noncomputable def bx4 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 30720 39936)

theorem wk4 : SixW15ST.walk bits 64 4944 bx4 = some 5445 := by decide +kernel

noncomputable def bx5 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 31744 37888 89088 237568 57856 401408)

theorem wk5 : SixW15ST.walk bits 64 5445 bx5 = some 5746 := by decide +kernel

noncomputable def bx6 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 30720 39936)

theorem wk6 : SixW15ST.walk bits 64 5746 bx6 = some 7112 := by decide +kernel

noncomputable def bx7 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 60416 73728 31744 38400 57856 401408)

theorem wk7 : SixW15ST.walk bits 64 7112 bx7 = some 8473 := by decide +kernel

noncomputable def bx8 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 30720 39936)

theorem wk8 : SixW15ST.walk bits 64 8473 bx8 = some 9029 := by decide +kernel

noncomputable def bx9 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 60416 73728 60416 74240 57856 401408)

theorem wk9 : SixW15ST.walk bits 64 9029 bx9 = some 9285 := by decide +kernel

noncomputable def bx10 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 30720 39936)

theorem wk10 : SixW15ST.walk bits 64 9285 bx10 = some 9366 := by decide +kernel

noncomputable def bx11 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 60416 73728 89088 237568 57856 401408)

theorem wk11 : SixW15ST.walk bits 64 9366 bx11 = some 9367 := by decide +kernel

noncomputable def bx12 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 30720 39936)

theorem wk12 : SixW15ST.walk bits 64 9367 bx12 = some 9718 := by decide +kernel

noncomputable def bx13 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 89600 221184 31744 38400 57856 401408)

theorem wk13 : SixW15ST.walk bits 64 9718 bx13 = some 9904 := by decide +kernel

noncomputable def bx14 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 30720 39936)

theorem wk14 : SixW15ST.walk bits 64 9904 bx14 = some 9950 := by decide +kernel

noncomputable def bx15 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 89600 221184 60416 74240 57856 401408)

theorem wk15 : SixW15ST.walk bits 64 9950 bx15 = some 9951 := by decide +kernel

noncomputable def bx16 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 30720 39936)

theorem wk16 : SixW15ST.walk bits 64 9951 bx16 = some 9952 := by decide +kernel

noncomputable def bx17 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 31744 38400 89600 221184 89088 237568 57856 401408)

theorem wk17 : SixW15ST.walk bits 64 9952 bx17 = some 9953 := by decide +kernel

noncomputable def bx18 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 30720 39936)

theorem wk18 : SixW15ST.walk bits 64 9953 bx18 = some 11064 := by decide +kernel

noncomputable def bx19 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 31744 37888 31744 38400 57856 401408)

theorem wk19 : SixW15ST.walk bits 64 11064 bx19 = some 12810 := by decide +kernel

noncomputable def bx20 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 30720 39936)

theorem wk20 : SixW15ST.walk bits 64 12810 bx20 = some 13921 := by decide +kernel

noncomputable def bx21 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 31744 37888 60416 74240 57856 401408)

theorem wk21 : SixW15ST.walk bits 64 13921 bx21 = some 14327 := by decide +kernel

noncomputable def bx22 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 30720 39936)

theorem wk22 : SixW15ST.walk bits 64 14327 bx22 = some 14443 := by decide +kernel

noncomputable def bx23 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 31744 37888 89088 237568 57856 401408)

theorem wk23 : SixW15ST.walk bits 64 14443 bx23 = some 14474 := by decide +kernel

noncomputable def bx24 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 30720 39936)

theorem wk24 : SixW15ST.walk bits 64 14474 bx24 = some 14990 := by decide +kernel

noncomputable def bx25 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 60416 73728 31744 38400 57856 401408)

theorem wk25 : SixW15ST.walk bits 64 14990 bx25 = some 15286 := by decide +kernel

noncomputable def bx26 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 30720 39936)

theorem wk26 : SixW15ST.walk bits 64 15286 bx26 = some 15347 := by decide +kernel

noncomputable def bx27 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 60416 73728 60416 74240 57856 401408)

theorem wk27 : SixW15ST.walk bits 64 15347 bx27 = some 15348 := by decide +kernel

noncomputable def bx28 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 30720 39936)

theorem wk28 : SixW15ST.walk bits 64 15348 bx28 = some 15349 := by decide +kernel

noncomputable def bx29 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 60416 73728 89088 237568 57856 401408)

theorem wk29 : SixW15ST.walk bits 64 15349 bx29 = some 15350 := by decide +kernel

noncomputable def bx30 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 30720 39936)

theorem wk30 : SixW15ST.walk bits 64 15350 bx30 = some 15396 := by decide +kernel

noncomputable def bx31 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 89600 221184 31744 38400 57856 401408)

theorem wk31 : SixW15ST.walk bits 64 15396 bx31 = some 15397 := by decide +kernel

noncomputable def bx32 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 30720 39936)

theorem wk32 : SixW15ST.walk bits 64 15397 bx32 = some 15398 := by decide +kernel

noncomputable def bx33 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 89600 221184 60416 74240 57856 401408)

theorem wk33 : SixW15ST.walk bits 64 15398 bx33 = some 15399 := by decide +kernel

noncomputable def bx34 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 30720 39936)

theorem wk34 : SixW15ST.walk bits 64 15399 bx34 = some 15400 := by decide +kernel

noncomputable def bx35 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 60416 74240 89600 221184 89088 237568 57856 401408)

theorem wk35 : SixW15ST.walk bits 64 15400 bx35 = some 15401 := by decide +kernel

noncomputable def bx36 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 30720 39936)

theorem wk36 : SixW15ST.walk bits 64 15401 bx36 = some 15897 := by decide +kernel

noncomputable def bx37 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 31744 37888 31744 38400 57856 401408)

theorem wk37 : SixW15ST.walk bits 64 15897 bx37 = some 16228 := by decide +kernel

noncomputable def bx38 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 30720 39936)

theorem wk38 : SixW15ST.walk bits 64 16228 bx38 = some 16344 := by decide +kernel

noncomputable def bx39 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 31744 37888 60416 74240 57856 401408)

theorem wk39 : SixW15ST.walk bits 64 16344 bx39 = some 16375 := by decide +kernel

noncomputable def bx40 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 30720 39936)

theorem wk40 : SixW15ST.walk bits 64 16375 bx40 = some 16376 := by decide +kernel

noncomputable def bx41 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 31744 37888 89088 237568 57856 401408)

theorem wk41 : SixW15ST.walk bits 64 16376 bx41 = some 16377 := by decide +kernel

noncomputable def bx42 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 30720 39936)

theorem wk42 : SixW15ST.walk bits 64 16377 bx42 = some 16458 := by decide +kernel

noncomputable def bx43 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 60416 73728 31744 38400 57856 401408)

theorem wk43 : SixW15ST.walk bits 64 16458 bx43 = some 16459 := by decide +kernel

noncomputable def bx44 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 30720 39936)

theorem wk44 : SixW15ST.walk bits 64 16459 bx44 = some 16460 := by decide +kernel

noncomputable def bx45 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 60416 73728 60416 74240 57856 401408)

theorem wk45 : SixW15ST.walk bits 64 16460 bx45 = some 16461 := by decide +kernel

noncomputable def bx46 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 30720 39936)

theorem wk46 : SixW15ST.walk bits 64 16461 bx46 = some 16462 := by decide +kernel

noncomputable def bx47 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 60416 73728 89088 237568 57856 401408)

theorem wk47 : SixW15ST.walk bits 64 16462 bx47 = some 16463 := by decide +kernel

noncomputable def bx48 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 30720 39936)

theorem wk48 : SixW15ST.walk bits 64 16463 bx48 = some 16464 := by decide +kernel

noncomputable def bx49 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 89600 221184 31744 38400 57856 401408)

theorem wk49 : SixW15ST.walk bits 64 16464 bx49 = some 16465 := by decide +kernel

noncomputable def bx50 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 30720 39936)

theorem wk50 : SixW15ST.walk bits 64 16465 bx50 = some 16466 := by decide +kernel

noncomputable def bx51 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 89600 221184 60416 74240 57856 401408)

theorem wk51 : SixW15ST.walk bits 64 16466 bx51 = some 16467 := by decide +kernel

noncomputable def bx52 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 30720 39936)

theorem wk52 : SixW15ST.walk bits 64 16467 bx52 = some 16468 := by decide +kernel

noncomputable def bx53 : SixW15ST.Box := (SixW15ST.Box.mk 30720 39936 89088 237568 89600 221184 89088 237568 57856 401408)

theorem wk53 : SixW15ST.walk bits 64 16468 bx53 = some 16469 := by decide +kernel

noncomputable def bx54 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 30720 39936)

theorem wk54 : SixW15ST.walk bits 64 16469 bx54 = some 16470 := by decide +kernel

noncomputable def bx55 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 31744 37888 31744 38400 57856 401408)

theorem wk55 : SixW15ST.walk bits 64 16470 bx55 = some 18321 := by decide +kernel

noncomputable def bx56 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 30720 39936)

theorem wk56 : SixW15ST.walk bits 64 18321 bx56 = some 18322 := by decide +kernel

noncomputable def bx57 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 31744 37888 60416 74240 57856 401408)

theorem wk57 : SixW15ST.walk bits 64 18322 bx57 = some 19163 := by decide +kernel

noncomputable def bx58 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 30720 39936)

theorem wk58 : SixW15ST.walk bits 64 19163 bx58 = some 19164 := by decide +kernel

noncomputable def bx59 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 31744 37888 89088 237568 57856 401408)

theorem wk59 : SixW15ST.walk bits 64 19164 bx59 = some 19260 := by decide +kernel

noncomputable def bx60 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 30720 39936)

theorem wk60 : SixW15ST.walk bits 64 19260 bx60 = some 19261 := by decide +kernel

noncomputable def bx61 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 60416 73728 31744 38400 57856 401408)

theorem wk61 : SixW15ST.walk bits 64 19261 bx61 = some 20092 := by decide +kernel

noncomputable def bx62 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 30720 39936)

theorem wk62 : SixW15ST.walk bits 64 20092 bx62 = some 20093 := by decide +kernel

noncomputable def bx63 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 60416 73728 60416 74240 57856 401408)

theorem wk63 : SixW15ST.walk bits 64 20093 bx63 = some 20169 := by decide +kernel

noncomputable def bx64 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 30720 39936)

theorem wk64 : SixW15ST.walk bits 64 20169 bx64 = some 20170 := by decide +kernel

noncomputable def bx65 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 60416 73728 89088 237568 57856 401408)

theorem wk65 : SixW15ST.walk bits 64 20170 bx65 = some 20171 := by decide +kernel

noncomputable def bx66 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 30720 39936)

theorem wk66 : SixW15ST.walk bits 64 20171 bx66 = some 20172 := by decide +kernel

noncomputable def bx67 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 89600 221184 31744 38400 57856 401408)

theorem wk67 : SixW15ST.walk bits 64 20172 bx67 = some 20253 := by decide +kernel

noncomputable def bx68 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 30720 39936)

theorem wk68 : SixW15ST.walk bits 64 20253 bx68 = some 20254 := by decide +kernel

noncomputable def bx69 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 89600 221184 60416 74240 57856 401408)

theorem wk69 : SixW15ST.walk bits 64 20254 bx69 = some 20255 := by decide +kernel

noncomputable def bx70 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 30720 39936)

theorem wk70 : SixW15ST.walk bits 64 20255 bx70 = some 20256 := by decide +kernel

noncomputable def bx71 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 31744 38400 89600 221184 89088 237568 57856 401408)

theorem wk71 : SixW15ST.walk bits 64 20256 bx71 = some 20257 := by decide +kernel

noncomputable def bx72 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 30720 39936)

theorem wk72 : SixW15ST.walk bits 64 20257 bx72 = some 20258 := by decide +kernel

noncomputable def bx73 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 31744 37888 31744 38400 57856 401408)

theorem wk73 : SixW15ST.walk bits 64 20258 bx73 = some 21084 := by decide +kernel

noncomputable def bx74 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 30720 39936)

theorem wk74 : SixW15ST.walk bits 64 21084 bx74 = some 21085 := by decide +kernel

noncomputable def bx75 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 31744 37888 60416 74240 57856 401408)

theorem wk75 : SixW15ST.walk bits 64 21085 bx75 = some 21171 := by decide +kernel

noncomputable def bx76 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 30720 39936)

theorem wk76 : SixW15ST.walk bits 64 21171 bx76 = some 21172 := by decide +kernel

noncomputable def bx77 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 31744 37888 89088 237568 57856 401408)

theorem wk77 : SixW15ST.walk bits 64 21172 bx77 = some 21173 := by decide +kernel

noncomputable def bx78 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 30720 39936)

theorem wk78 : SixW15ST.walk bits 64 21173 bx78 = some 21174 := by decide +kernel

noncomputable def bx79 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 60416 73728 31744 38400 57856 401408)

theorem wk79 : SixW15ST.walk bits 64 21174 bx79 = some 21250 := by decide +kernel

noncomputable def bx80 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 30720 39936)

theorem wk80 : SixW15ST.walk bits 64 21250 bx80 = some 21251 := by decide +kernel

noncomputable def bx81 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 60416 73728 60416 74240 57856 401408)

theorem wk81 : SixW15ST.walk bits 64 21251 bx81 = some 21252 := by decide +kernel

noncomputable def bx82 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 30720 39936)

theorem wk82 : SixW15ST.walk bits 64 21252 bx82 = some 21253 := by decide +kernel

noncomputable def bx83 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 60416 73728 89088 237568 57856 401408)

theorem wk83 : SixW15ST.walk bits 64 21253 bx83 = some 21254 := by decide +kernel

noncomputable def bx84 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 30720 39936)

theorem wk84 : SixW15ST.walk bits 64 21254 bx84 = some 21255 := by decide +kernel

noncomputable def bx85 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 89600 221184 31744 38400 57856 401408)

theorem wk85 : SixW15ST.walk bits 64 21255 bx85 = some 21256 := by decide +kernel

noncomputable def bx86 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 30720 39936)

theorem wk86 : SixW15ST.walk bits 64 21256 bx86 = some 21257 := by decide +kernel

noncomputable def bx87 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 89600 221184 60416 74240 57856 401408)

theorem wk87 : SixW15ST.walk bits 64 21257 bx87 = some 21258 := by decide +kernel

noncomputable def bx88 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 30720 39936)

theorem wk88 : SixW15ST.walk bits 64 21258 bx88 = some 21259 := by decide +kernel

noncomputable def bx89 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 60416 74240 89600 221184 89088 237568 57856 401408)

theorem wk89 : SixW15ST.walk bits 64 21259 bx89 = some 21260 := by decide +kernel

noncomputable def bx90 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 30720 39936)

theorem wk90 : SixW15ST.walk bits 64 21260 bx90 = some 21261 := by decide +kernel

noncomputable def bx91 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 31744 37888 31744 38400 57856 401408)

theorem wk91 : SixW15ST.walk bits 64 21261 bx91 = some 21357 := by decide +kernel

noncomputable def bx92 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 30720 39936)

theorem wk92 : SixW15ST.walk bits 64 21357 bx92 = some 21358 := by decide +kernel

noncomputable def bx93 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 31744 37888 60416 74240 57856 401408)

theorem wk93 : SixW15ST.walk bits 64 21358 bx93 = some 21359 := by decide +kernel

noncomputable def bx94 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 30720 39936)

theorem wk94 : SixW15ST.walk bits 64 21359 bx94 = some 21360 := by decide +kernel

noncomputable def bx95 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 31744 37888 89088 237568 57856 401408)

theorem wk95 : SixW15ST.walk bits 64 21360 bx95 = some 21361 := by decide +kernel

noncomputable def bx96 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 30720 39936)

theorem wk96 : SixW15ST.walk bits 64 21361 bx96 = some 21362 := by decide +kernel

noncomputable def bx97 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 60416 73728 31744 38400 57856 401408)

theorem wk97 : SixW15ST.walk bits 64 21362 bx97 = some 21363 := by decide +kernel

noncomputable def bx98 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 30720 39936)

theorem wk98 : SixW15ST.walk bits 64 21363 bx98 = some 21364 := by decide +kernel

noncomputable def bx99 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 60416 73728 60416 74240 57856 401408)

theorem wk99 : SixW15ST.walk bits 64 21364 bx99 = some 21365 := by decide +kernel

noncomputable def bx100 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 30720 39936)

theorem wk100 : SixW15ST.walk bits 64 21365 bx100 = some 21366 := by decide +kernel

noncomputable def bx101 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 60416 73728 89088 237568 57856 401408)

theorem wk101 : SixW15ST.walk bits 64 21366 bx101 = some 21367 := by decide +kernel

noncomputable def bx102 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 30720 39936)

theorem wk102 : SixW15ST.walk bits 64 21367 bx102 = some 21368 := by decide +kernel

noncomputable def bx103 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 89600 221184 31744 38400 57856 401408)

theorem wk103 : SixW15ST.walk bits 64 21368 bx103 = some 21369 := by decide +kernel

noncomputable def bx104 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 30720 39936)

theorem wk104 : SixW15ST.walk bits 64 21369 bx104 = some 21370 := by decide +kernel

noncomputable def bx105 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 89600 221184 60416 74240 57856 401408)

theorem wk105 : SixW15ST.walk bits 64 21370 bx105 = some 21371 := by decide +kernel

noncomputable def bx106 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 30720 39936)

theorem wk106 : SixW15ST.walk bits 64 21371 bx106 = some 21372 := by decide +kernel

noncomputable def bx107 : SixW15ST.Box := (SixW15ST.Box.mk 57856 401408 89088 237568 89600 221184 89088 237568 57856 401408)

theorem wk107 : SixW15ST.walk bits 64 21372 bx107 = some 21373 := by decide +kernel

theorem nb0_eq : (SixW15ST.badOf cover0).length = 2 := by decide +kernel

theorem nb1_eq : (SixW15ST.badOf cover1).length = 3 := by decide +kernel

theorem nb2_eq : (SixW15ST.badOf cover2).length = 3 := by decide +kernel

theorem nb3_eq : (SixW15ST.badOf cover3).length = 3 := by decide +kernel

theorem nb4_eq : (SixW15ST.badOf cover4).length = 2 := by decide +kernel

theorem root_00000 : SixW15ST.walk bits 64 0 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 0 0) = some 721 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 0 0 = bx0 from by decide +kernel]; exact wk0

theorem root_00001 : SixW15ST.walk bits 64 721 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 0 1) = some 2527 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 0 1 = bx1 from by decide +kernel]; exact wk1

theorem root_00010 : SixW15ST.walk bits 64 2527 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 1 0) = some 3658 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 1 0 = bx2 from by decide +kernel]; exact wk2

theorem root_00011 : SixW15ST.walk bits 64 3658 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 1 1) = some 4944 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 1 1 = bx3 from by decide +kernel]; exact wk3

theorem root_00020 : SixW15ST.walk bits 64 4944 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 2 0) = some 5445 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 2 0 = bx4 from by decide +kernel]; exact wk4

theorem root_00021 : SixW15ST.walk bits 64 5445 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 2 1) = some 5746 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 0 2 1 = bx5 from by decide +kernel]; exact wk5

theorem root_00100 : SixW15ST.walk bits 64 5746 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 0 0) = some 7112 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 0 0 = bx6 from by decide +kernel]; exact wk6

theorem root_00101 : SixW15ST.walk bits 64 7112 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 0 1) = some 8473 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 0 1 = bx7 from by decide +kernel]; exact wk7

theorem root_00110 : SixW15ST.walk bits 64 8473 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 1 0) = some 9029 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 1 0 = bx8 from by decide +kernel]; exact wk8

theorem root_00111 : SixW15ST.walk bits 64 9029 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 1 1) = some 9285 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 1 1 = bx9 from by decide +kernel]; exact wk9

theorem root_00120 : SixW15ST.walk bits 64 9285 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 2 0) = some 9366 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 2 0 = bx10 from by decide +kernel]; exact wk10

theorem root_00121 : SixW15ST.walk bits 64 9366 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 2 1) = some 9367 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 1 2 1 = bx11 from by decide +kernel]; exact wk11

theorem root_00200 : SixW15ST.walk bits 64 9367 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 0 0) = some 9718 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 0 0 = bx12 from by decide +kernel]; exact wk12

theorem root_00201 : SixW15ST.walk bits 64 9718 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 0 1) = some 9904 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 0 1 = bx13 from by decide +kernel]; exact wk13

theorem root_00210 : SixW15ST.walk bits 64 9904 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 1 0) = some 9950 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 1 0 = bx14 from by decide +kernel]; exact wk14

theorem root_00211 : SixW15ST.walk bits 64 9950 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 1 1) = some 9951 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 1 1 = bx15 from by decide +kernel]; exact wk15

theorem root_00220 : SixW15ST.walk bits 64 9951 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 2 0) = some 9952 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 2 0 = bx16 from by decide +kernel]; exact wk16

theorem root_00221 : SixW15ST.walk bits 64 9952 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 2 1) = some 9953 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 0 2 2 1 = bx17 from by decide +kernel]; exact wk17

theorem root_01000 : SixW15ST.walk bits 64 9953 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 0 0) = some 11064 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 0 0 = bx18 from by decide +kernel]; exact wk18

theorem root_01001 : SixW15ST.walk bits 64 11064 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 0 1) = some 12810 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 0 1 = bx19 from by decide +kernel]; exact wk19

theorem root_01010 : SixW15ST.walk bits 64 12810 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 1 0) = some 13921 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 1 0 = bx20 from by decide +kernel]; exact wk20

theorem root_01011 : SixW15ST.walk bits 64 13921 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 1 1) = some 14327 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 1 1 = bx21 from by decide +kernel]; exact wk21

theorem root_01020 : SixW15ST.walk bits 64 14327 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 2 0) = some 14443 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 2 0 = bx22 from by decide +kernel]; exact wk22

theorem root_01021 : SixW15ST.walk bits 64 14443 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 2 1) = some 14474 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 0 2 1 = bx23 from by decide +kernel]; exact wk23

theorem root_01100 : SixW15ST.walk bits 64 14474 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 0 0) = some 14990 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 0 0 = bx24 from by decide +kernel]; exact wk24

theorem root_01101 : SixW15ST.walk bits 64 14990 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 0 1) = some 15286 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 0 1 = bx25 from by decide +kernel]; exact wk25

theorem root_01110 : SixW15ST.walk bits 64 15286 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 1 0) = some 15347 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 1 0 = bx26 from by decide +kernel]; exact wk26

theorem root_01111 : SixW15ST.walk bits 64 15347 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 1 1) = some 15348 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 1 1 = bx27 from by decide +kernel]; exact wk27

theorem root_01120 : SixW15ST.walk bits 64 15348 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 2 0) = some 15349 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 2 0 = bx28 from by decide +kernel]; exact wk28

theorem root_01121 : SixW15ST.walk bits 64 15349 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 2 1) = some 15350 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 1 2 1 = bx29 from by decide +kernel]; exact wk29

theorem root_01200 : SixW15ST.walk bits 64 15350 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 0 0) = some 15396 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 0 0 = bx30 from by decide +kernel]; exact wk30

theorem root_01201 : SixW15ST.walk bits 64 15396 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 0 1) = some 15397 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 0 1 = bx31 from by decide +kernel]; exact wk31

theorem root_01210 : SixW15ST.walk bits 64 15397 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 1 0) = some 15398 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 1 0 = bx32 from by decide +kernel]; exact wk32

theorem root_01211 : SixW15ST.walk bits 64 15398 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 1 1) = some 15399 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 1 1 = bx33 from by decide +kernel]; exact wk33

theorem root_01220 : SixW15ST.walk bits 64 15399 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 2 0) = some 15400 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 2 0 = bx34 from by decide +kernel]; exact wk34

theorem root_01221 : SixW15ST.walk bits 64 15400 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 2 1) = some 15401 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 1 2 2 1 = bx35 from by decide +kernel]; exact wk35

theorem root_02000 : SixW15ST.walk bits 64 15401 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 0 0) = some 15897 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 0 0 = bx36 from by decide +kernel]; exact wk36

theorem root_02001 : SixW15ST.walk bits 64 15897 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 0 1) = some 16228 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 0 1 = bx37 from by decide +kernel]; exact wk37

theorem root_02010 : SixW15ST.walk bits 64 16228 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 1 0) = some 16344 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 1 0 = bx38 from by decide +kernel]; exact wk38

theorem root_02011 : SixW15ST.walk bits 64 16344 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 1 1) = some 16375 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 1 1 = bx39 from by decide +kernel]; exact wk39

theorem root_02020 : SixW15ST.walk bits 64 16375 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 2 0) = some 16376 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 2 0 = bx40 from by decide +kernel]; exact wk40

theorem root_02021 : SixW15ST.walk bits 64 16376 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 2 1) = some 16377 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 0 2 1 = bx41 from by decide +kernel]; exact wk41

theorem root_02100 : SixW15ST.walk bits 64 16377 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 0 0) = some 16458 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 0 0 = bx42 from by decide +kernel]; exact wk42

theorem root_02101 : SixW15ST.walk bits 64 16458 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 0 1) = some 16459 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 0 1 = bx43 from by decide +kernel]; exact wk43

theorem root_02110 : SixW15ST.walk bits 64 16459 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 1 0) = some 16460 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 1 0 = bx44 from by decide +kernel]; exact wk44

theorem root_02111 : SixW15ST.walk bits 64 16460 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 1 1) = some 16461 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 1 1 = bx45 from by decide +kernel]; exact wk45

theorem root_02120 : SixW15ST.walk bits 64 16461 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 2 0) = some 16462 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 2 0 = bx46 from by decide +kernel]; exact wk46

theorem root_02121 : SixW15ST.walk bits 64 16462 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 2 1) = some 16463 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 1 2 1 = bx47 from by decide +kernel]; exact wk47

theorem root_02200 : SixW15ST.walk bits 64 16463 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 0 0) = some 16464 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 0 0 = bx48 from by decide +kernel]; exact wk48

theorem root_02201 : SixW15ST.walk bits 64 16464 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 0 1) = some 16465 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 0 1 = bx49 from by decide +kernel]; exact wk49

theorem root_02210 : SixW15ST.walk bits 64 16465 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 1 0) = some 16466 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 1 0 = bx50 from by decide +kernel]; exact wk50

theorem root_02211 : SixW15ST.walk bits 64 16466 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 1 1) = some 16467 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 1 1 = bx51 from by decide +kernel]; exact wk51

theorem root_02220 : SixW15ST.walk bits 64 16467 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 2 0) = some 16468 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 2 0 = bx52 from by decide +kernel]; exact wk52

theorem root_02221 : SixW15ST.walk bits 64 16468 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 2 1) = some 16469 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 0 2 2 2 1 = bx53 from by decide +kernel]; exact wk53

theorem root_10000 : SixW15ST.walk bits 64 16469 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 0 0) = some 16470 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 0 0 = bx54 from by decide +kernel]; exact wk54

theorem root_10001 : SixW15ST.walk bits 64 16470 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 0 1) = some 18321 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 0 1 = bx55 from by decide +kernel]; exact wk55

theorem root_10010 : SixW15ST.walk bits 64 18321 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 1 0) = some 18322 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 1 0 = bx56 from by decide +kernel]; exact wk56

theorem root_10011 : SixW15ST.walk bits 64 18322 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 1 1) = some 19163 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 1 1 = bx57 from by decide +kernel]; exact wk57

theorem root_10020 : SixW15ST.walk bits 64 19163 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 2 0) = some 19164 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 2 0 = bx58 from by decide +kernel]; exact wk58

theorem root_10021 : SixW15ST.walk bits 64 19164 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 2 1) = some 19260 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 0 2 1 = bx59 from by decide +kernel]; exact wk59

theorem root_10100 : SixW15ST.walk bits 64 19260 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 0 0) = some 19261 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 0 0 = bx60 from by decide +kernel]; exact wk60

theorem root_10101 : SixW15ST.walk bits 64 19261 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 0 1) = some 20092 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 0 1 = bx61 from by decide +kernel]; exact wk61

theorem root_10110 : SixW15ST.walk bits 64 20092 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 1 0) = some 20093 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 1 0 = bx62 from by decide +kernel]; exact wk62

theorem root_10111 : SixW15ST.walk bits 64 20093 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 1 1) = some 20169 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 1 1 = bx63 from by decide +kernel]; exact wk63

theorem root_10120 : SixW15ST.walk bits 64 20169 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 2 0) = some 20170 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 2 0 = bx64 from by decide +kernel]; exact wk64

theorem root_10121 : SixW15ST.walk bits 64 20170 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 2 1) = some 20171 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 1 2 1 = bx65 from by decide +kernel]; exact wk65

theorem root_10200 : SixW15ST.walk bits 64 20171 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 0 0) = some 20172 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 0 0 = bx66 from by decide +kernel]; exact wk66

theorem root_10201 : SixW15ST.walk bits 64 20172 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 0 1) = some 20253 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 0 1 = bx67 from by decide +kernel]; exact wk67

theorem root_10210 : SixW15ST.walk bits 64 20253 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 1 0) = some 20254 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 1 0 = bx68 from by decide +kernel]; exact wk68

theorem root_10211 : SixW15ST.walk bits 64 20254 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 1 1) = some 20255 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 1 1 = bx69 from by decide +kernel]; exact wk69

theorem root_10220 : SixW15ST.walk bits 64 20255 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 2 0) = some 20256 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 2 0 = bx70 from by decide +kernel]; exact wk70

theorem root_10221 : SixW15ST.walk bits 64 20256 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 2 1) = some 20257 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 0 2 2 1 = bx71 from by decide +kernel]; exact wk71

theorem root_11000 : SixW15ST.walk bits 64 20257 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 0 0) = some 20258 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 0 0 = bx72 from by decide +kernel]; exact wk72

theorem root_11001 : SixW15ST.walk bits 64 20258 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 0 1) = some 21084 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 0 1 = bx73 from by decide +kernel]; exact wk73

theorem root_11010 : SixW15ST.walk bits 64 21084 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 1 0) = some 21085 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 1 0 = bx74 from by decide +kernel]; exact wk74

theorem root_11011 : SixW15ST.walk bits 64 21085 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 1 1) = some 21171 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 1 1 = bx75 from by decide +kernel]; exact wk75

theorem root_11020 : SixW15ST.walk bits 64 21171 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 2 0) = some 21172 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 2 0 = bx76 from by decide +kernel]; exact wk76

theorem root_11021 : SixW15ST.walk bits 64 21172 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 2 1) = some 21173 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 0 2 1 = bx77 from by decide +kernel]; exact wk77

theorem root_11100 : SixW15ST.walk bits 64 21173 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 0 0) = some 21174 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 0 0 = bx78 from by decide +kernel]; exact wk78

theorem root_11101 : SixW15ST.walk bits 64 21174 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 0 1) = some 21250 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 0 1 = bx79 from by decide +kernel]; exact wk79

theorem root_11110 : SixW15ST.walk bits 64 21250 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 1 0) = some 21251 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 1 0 = bx80 from by decide +kernel]; exact wk80

theorem root_11111 : SixW15ST.walk bits 64 21251 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 1 1) = some 21252 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 1 1 = bx81 from by decide +kernel]; exact wk81

theorem root_11120 : SixW15ST.walk bits 64 21252 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 2 0) = some 21253 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 2 0 = bx82 from by decide +kernel]; exact wk82

theorem root_11121 : SixW15ST.walk bits 64 21253 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 2 1) = some 21254 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 1 2 1 = bx83 from by decide +kernel]; exact wk83

theorem root_11200 : SixW15ST.walk bits 64 21254 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 0 0) = some 21255 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 0 0 = bx84 from by decide +kernel]; exact wk84

theorem root_11201 : SixW15ST.walk bits 64 21255 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 0 1) = some 21256 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 0 1 = bx85 from by decide +kernel]; exact wk85

theorem root_11210 : SixW15ST.walk bits 64 21256 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 1 0) = some 21257 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 1 0 = bx86 from by decide +kernel]; exact wk86

theorem root_11211 : SixW15ST.walk bits 64 21257 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 1 1) = some 21258 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 1 1 = bx87 from by decide +kernel]; exact wk87

theorem root_11220 : SixW15ST.walk bits 64 21258 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 2 0) = some 21259 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 2 0 = bx88 from by decide +kernel]; exact wk88

theorem root_11221 : SixW15ST.walk bits 64 21259 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 2 1) = some 21260 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 1 2 2 1 = bx89 from by decide +kernel]; exact wk89

theorem root_12000 : SixW15ST.walk bits 64 21260 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 0 0) = some 21261 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 0 0 = bx90 from by decide +kernel]; exact wk90

theorem root_12001 : SixW15ST.walk bits 64 21261 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 0 1) = some 21357 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 0 1 = bx91 from by decide +kernel]; exact wk91

theorem root_12010 : SixW15ST.walk bits 64 21357 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 1 0) = some 21358 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 1 0 = bx92 from by decide +kernel]; exact wk92

theorem root_12011 : SixW15ST.walk bits 64 21358 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 1 1) = some 21359 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 1 1 = bx93 from by decide +kernel]; exact wk93

theorem root_12020 : SixW15ST.walk bits 64 21359 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 2 0) = some 21360 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 2 0 = bx94 from by decide +kernel]; exact wk94

theorem root_12021 : SixW15ST.walk bits 64 21360 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 2 1) = some 21361 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 0 2 1 = bx95 from by decide +kernel]; exact wk95

theorem root_12100 : SixW15ST.walk bits 64 21361 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 0 0) = some 21362 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 0 0 = bx96 from by decide +kernel]; exact wk96

theorem root_12101 : SixW15ST.walk bits 64 21362 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 0 1) = some 21363 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 0 1 = bx97 from by decide +kernel]; exact wk97

theorem root_12110 : SixW15ST.walk bits 64 21363 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 1 0) = some 21364 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 1 0 = bx98 from by decide +kernel]; exact wk98

theorem root_12111 : SixW15ST.walk bits 64 21364 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 1 1) = some 21365 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 1 1 = bx99 from by decide +kernel]; exact wk99

theorem root_12120 : SixW15ST.walk bits 64 21365 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 2 0) = some 21366 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 2 0 = bx100 from by decide +kernel]; exact wk100

theorem root_12121 : SixW15ST.walk bits 64 21366 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 2 1) = some 21367 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 1 2 1 = bx101 from by decide +kernel]; exact wk101

theorem root_12200 : SixW15ST.walk bits 64 21367 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 0 0) = some 21368 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 0 0 = bx102 from by decide +kernel]; exact wk102

theorem root_12201 : SixW15ST.walk bits 64 21368 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 0 1) = some 21369 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 0 1 = bx103 from by decide +kernel]; exact wk103

theorem root_12210 : SixW15ST.walk bits 64 21369 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 1 0) = some 21370 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 1 0 = bx104 from by decide +kernel]; exact wk104

theorem root_12211 : SixW15ST.walk bits 64 21370 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 1 1) = some 21371 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 1 1 = bx105 from by decide +kernel]; exact wk105

theorem root_12220 : SixW15ST.walk bits 64 21371 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 2 0) = some 21372 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 2 0 = bx106 from by decide +kernel]; exact wk106

theorem root_12221 : SixW15ST.walk bits 64 21372 (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 2 1) = some 21373 := by
  rw [show SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) 1 2 2 2 1 = bx107 from by decide +kernel]; exact wk107

theorem run_ok : ∀ i0 i1 i2 i3 i4, i0 < (SixW15ST.badOf cover0).length → i1 < (SixW15ST.badOf cover1).length → i2 < (SixW15ST.badOf cover2).length → i3 < (SixW15ST.badOf cover3).length → i4 < (SixW15ST.badOf cover4).length →
    ∃ pos pos', SixW15ST.walk bits 64 pos (SixW15ST.boxOf (SixW15ST.badOf cover0) (SixW15ST.badOf cover1) (SixW15ST.badOf cover2) (SixW15ST.badOf cover3) (SixW15ST.badOf cover4) i0 i1 i2 i3 i4) = some pos' := by
  intro i0 i1 i2 i3 i4 hi0 hi1 hi2 hi3 hi4
  rw [nb0_eq] at hi0
  rw [nb1_eq] at hi1
  rw [nb2_eq] at hi2
  rw [nb3_eq] at hi3
  rw [nb4_eq] at hi4
  match i0, i1, i2, i3, i4, hi0, hi1, hi2, hi3, hi4 with
  | 0, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00000⟩
  | 0, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00001⟩
  | 0, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00010⟩
  | 0, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00011⟩
  | 0, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00020⟩
  | 0, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00021⟩
  | 0, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00100⟩
  | 0, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00101⟩
  | 0, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00110⟩
  | 0, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00111⟩
  | 0, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00120⟩
  | 0, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00121⟩
  | 0, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_00200⟩
  | 0, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_00201⟩
  | 0, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_00210⟩
  | 0, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_00211⟩
  | 0, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_00220⟩
  | 0, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_00221⟩
  | 0, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01000⟩
  | 0, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01001⟩
  | 0, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01010⟩
  | 0, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01011⟩
  | 0, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01020⟩
  | 0, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01021⟩
  | 0, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01100⟩
  | 0, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01101⟩
  | 0, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01110⟩
  | 0, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01111⟩
  | 0, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01120⟩
  | 0, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01121⟩
  | 0, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_01200⟩
  | 0, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_01201⟩
  | 0, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_01210⟩
  | 0, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_01211⟩
  | 0, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_01220⟩
  | 0, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_01221⟩
  | 0, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02000⟩
  | 0, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02001⟩
  | 0, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02010⟩
  | 0, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02011⟩
  | 0, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02020⟩
  | 0, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02021⟩
  | 0, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02100⟩
  | 0, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02101⟩
  | 0, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02110⟩
  | 0, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02111⟩
  | 0, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02120⟩
  | 0, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02121⟩
  | 0, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_02200⟩
  | 0, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_02201⟩
  | 0, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_02210⟩
  | 0, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_02211⟩
  | 0, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_02220⟩
  | 0, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_02221⟩
  | 1, 0, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10000⟩
  | 1, 0, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10001⟩
  | 1, 0, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10010⟩
  | 1, 0, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10011⟩
  | 1, 0, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10020⟩
  | 1, 0, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10021⟩
  | 1, 0, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10100⟩
  | 1, 0, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10101⟩
  | 1, 0, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10110⟩
  | 1, 0, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10111⟩
  | 1, 0, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10120⟩
  | 1, 0, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10121⟩
  | 1, 0, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_10200⟩
  | 1, 0, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_10201⟩
  | 1, 0, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_10210⟩
  | 1, 0, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_10211⟩
  | 1, 0, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_10220⟩
  | 1, 0, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_10221⟩
  | 1, 1, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11000⟩
  | 1, 1, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11001⟩
  | 1, 1, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11010⟩
  | 1, 1, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11011⟩
  | 1, 1, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11020⟩
  | 1, 1, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11021⟩
  | 1, 1, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11100⟩
  | 1, 1, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11101⟩
  | 1, 1, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11110⟩
  | 1, 1, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11111⟩
  | 1, 1, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11120⟩
  | 1, 1, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11121⟩
  | 1, 1, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_11200⟩
  | 1, 1, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_11201⟩
  | 1, 1, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_11210⟩
  | 1, 1, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_11211⟩
  | 1, 1, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_11220⟩
  | 1, 1, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_11221⟩
  | 1, 2, 0, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12000⟩
  | 1, 2, 0, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12001⟩
  | 1, 2, 0, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12010⟩
  | 1, 2, 0, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12011⟩
  | 1, 2, 0, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12020⟩
  | 1, 2, 0, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12021⟩
  | 1, 2, 1, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12100⟩
  | 1, 2, 1, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12101⟩
  | 1, 2, 1, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12110⟩
  | 1, 2, 1, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12111⟩
  | 1, 2, 1, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12120⟩
  | 1, 2, 1, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12121⟩
  | 1, 2, 2, 0, 0, _, _, _, _, _ => exact ⟨_, _, root_12200⟩
  | 1, 2, 2, 0, 1, _, _, _, _, _ => exact ⟨_, _, root_12201⟩
  | 1, 2, 2, 1, 0, _, _, _, _, _ => exact ⟨_, _, root_12210⟩
  | 1, 2, 2, 1, 1, _, _, _, _, _ => exact ⟨_, _, root_12211⟩
  | 1, 2, 2, 2, 0, _, _, _, _, _ => exact ⟨_, _, root_12220⟩
  | 1, 2, 2, 2, 1, _, _, _, _, _ => exact ⟨_, _, root_12221⟩
  | i + 2, _, _, _, _, hi, _, _, _, _ => exact absurd hi (by omega)
  | _, i + 3, _, _, _, _, hi, _, _, _ => exact absurd hi (by omega)
  | _, _, i + 3, _, _, _, _, hi, _, _ => exact absurd hi (by omega)
  | _, _, _, i + 3, _, _, _, _, hi, _ => exact absurd hi (by omega)
  | _, _, _, _, i + 2, _, _, _, _, hi => exact absurd hi (by omega)

theorem cert : ∀ g0 g1 g2 g3 g4 : ℝ, 0 ≤ g0 → 0 ≤ g1 → 0 ≤ g2 → 0 ≤ g3 → 0 ≤ g4 → (SixW15ST.cN : ℝ) / SixW15ST.SA ≤ SixW15ST.G g0 g1 g2 g3 g4 :=
  SixW15ST.of_check bits 64 cover0 cover1 cover2 cover3 cover4 401408 237568 221184 237568 401408
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) cover0_ok cover1_ok cover2_ok cover3_ok cover4_ok (by decide +kernel) run_ok


end Zeta23Ext.Bridge.ThreePoint.SixW15STData
