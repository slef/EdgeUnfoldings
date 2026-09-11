"""Schematic face-tree comparison; not a distortion of metric net geometry."""
from pathlib import Path


def build():
    out=['<svg xmlns="http://www.w3.org/2000/svg" width="860" height="690" viewBox="0 0 860 690" role="img" aria-labelledby="title desc">',
         '<title id="title">The same triangular chain inside two prism unfoldings</title>',
         '<desc id="desc">Remove four leaf triangles from the reference shortest-path star, or the two quadrilaterals from the original-edge fallback. Both leave the chain A, C, E, F with hinges 01, 13, 34. Hence the triangular caps A and F are disjoint in the fallback.</desc>',
         '<rect width="860" height="690" rx="14" fill="#f7fafc"/>',
         '<style>text{font-family:Arial,sans-serif;fill:#253e4b}.title{font-size:23px;font-weight:bold}.subtitle{font-size:17px}.face{font-size:21px;font-weight:bold}.edge{font-size:16px;fill:#4a6775}.note{font-size:17px}</style>']
    def text(x,y,s,cls='note',anchor='middle'):out.append(f'<text x="{x}" y="{y}" class="{cls}" text-anchor="{anchor}">{s}</text>')
    def line(x1,y1,x2,y2,label,ghost=False):
        out.append(f'<path d="M{x1} {y1}L{x2} {y2}" stroke="'+('#98aab4' if ghost else '#367b62')+f'" stroke-width="{2 if ghost else 4}"'+(' stroke-dasharray="5 5"' if ghost else '')+'/>')
        text((x1+x2)/2+(19 if x1==x2 else 0),(y1+y2)/2+(6 if x1==x2 else -8),label,'edge')
    def face(x,y,label,color='#edf2ef',ghost=False):
        out.append(f'<rect x="{x-46}" y="{y-23}" width="92" height="46" rx="8" fill="{color}" stroke="'+('#a6b4bc' if ghost else '#496774')+'" stroke-width="1.5"'+(' stroke-dasharray="5 4"' if ghost else '')+'/>')
        text(x,y+7,label,'face')
    text(35,36,'Why the triangular caps never meet','title','start')
    text(35,66,'A face-tree comparison: each line is an uncut hinge, not a drawn polyhedron edge.','subtitle','start')
    text(35,108,'1. Reference shortest-path star at vertex 2','title','start')
    xx=[95,315,535,755]
    y=222
    for a,b,h in zip(xx,xx[1:],['01','13','34']):line(a+46,y,b-46,y,h)
    for x,label in zip(xx,['A','C','E','F']):face(x,y,label)
    for x,yy,parent,h,label,color in [(315,153,315,'03','B₁','#d6e9f3'),(535,153,535,'14','D₁','#f2ddc4'),(755,153,755,'35','B₂','#d6e9f3'),(755,292,755,'45','D₂','#f2ddc4')]:
        line(parent,y-23 if yy<y else y+23,x,yy+23 if yy<y else yy-23,h,True);face(x,yy,label,color,True)
    text(35,285,'B is split along 23; D is split along 24.','note','start')
    text(35,311,'Delete the four dashed leaf pieces.','note','start')
    out.append('<path d="M35 340H825" stroke="#cfdae0"/>')
    text(35,379,'2. The original-edge fallback tree','title','start')
    y=503
    for a,b,h in zip(xx,xx[1:],['01','13','34']):line(a+46,y,b-46,y,h)
    for x,label in zip(xx,['A','C','E','F']):face(x,y,label)
    for x,label,h,color in [(315,'B','03','#b5d7e8'),(535,'D','14','#ebc392')]:
        line(x,y-23,x,437+23,h);face(x,437,label,color)
    text(35,555,'Delete the two whole quadrilaterals: the same A–C–E–F chain remains.','note','start')
    out.append('<rect x="35" y="584" width="790" height="76" rx="10" fill="#e3eee8"/>')
    text(55,614,'The chain inherits nonoverlap from the known star unfolding.','note','start')
    text(55,642,'Fourteen of fifteen pairs are safe. Only quadrilateral B versus D remains.','note','start')
    out.append('</svg>');return '\n'.join(out)+'\n'


if __name__=='__main__':(Path(__file__).parent/'figures/prism-one-pair-comparison.svg').write_text(build())
