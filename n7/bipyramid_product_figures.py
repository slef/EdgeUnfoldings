"""Plot exact-certificate ratios as rounded illustrations of the local rule."""
import json
from fractions import Fraction as F
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from n7.bipyramid_morph import ROOT

def build():
    rows=json.loads((ROOT/'results/bipyramid-product-rule.json').read_text())['examples'];fig,axs=plt.subplots(2,1,figsize=(11,5.5));fig.patch.set_facecolor('#fbfaf6')
    for ax,row,title in zip(axs,[rows[1],rows[3]],['A. Four inward corners: both poles pass','B. Three inward corners: the tests conflict']):
        c=row['certificate'];D=[float((F(x[0])+F(x[1]))/2) for x in c['pole_diagonals']];H=list(map(lambda x:float(F(x)),c['signed_squared_distance_differences']));bad=c['bad_vertices'];x=[H[i]/(D[(i-1)%5]*D[i]) for i in bad]
        ax.set_xlim(-2.1,2.9);ax.set_ylim(-.8,1.2);ax.axvspan(-1,1,color='#dcecdf');ax.axhline(0,color='#7b8c83',lw=1);ax.axvline(-1,color='#597d98',ls='--');ax.axvline(1,color='#ac754e',ls='--')
        for j,(i,z) in enumerate(zip(bad,x)):
            ax.plot(z,0,'o',color='#326d4c' if -1<=z<=1 else '#9e4a4a',markersize=7);ax.annotate('u'+str(i),(z,0),xytext=(0,16 if j%2==0 else -24),textcoords='offset points',ha='center',fontsize=11)
        ax.text(-2.0,.95,title,fontsize=13,fontweight='bold');ax.set_yticks([]);ax.set_xticks([-1,0,1]);ax.set_xticklabels(['−1','0','+1']);ax.spines[['top','left','right','bottom']].set_visible(False)
    fig.text(.08,.04,'Source q passes if every dot is at most +1. The opposite source passes if every dot is at least −1.',fontsize=11,color='#41565e');fig.subplots_adjust(left=.06,right=.98,top=.98,bottom=.12,hspace=.3);fig.savefig(ROOT/'figures/bipyramid-product-test.svg',facecolor=fig.get_facecolor());plt.close(fig)
if __name__=='__main__':build()
